import V185TrunkScan20Chunk047

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_292429 : List Nat := [1, 6, 1, 1, 3, 1, 2, 3, 2]
def baseStart_292429 : Nat := 118140960795 + 292429 * 2 ^ 59
def prefixEnd_292429 : Nat := 4983230072969 + 3 ^ 40 * 292429 * 2
def baseEnd_292429 : Nat := 133472563834436981237911

theorem tailTrace_292429 : CollatzResearch.WordTrace tailWord_292429 prefixEnd_292429 133472563834436981237911 := by
  unfold tailWord_292429
  simp only [CollatzResearch.WordTrace]
  refine ⟨10665761857587150742152341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7110507905058100494768227 10665761857587150742152341)
  ·
    refine ⟨499957587074397691038391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10665761857587150742152341 499957587074397691038391)
    ·
      refine ⟨749936380611596536557587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499957587074397691038391 749936380611596536557587)
      ·
        refine ⟨1124904570917394804836381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749936380611596536557587 1124904570917394804836381)
        ·
          refine ⟨421839214094023051813643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1124904570917394804836381 421839214094023051813643)
          ·
            refine ⟨632758821141034577720465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421839214094023051813643 632758821141034577720465)
            ·
              refine ⟨474569115855775933290349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 632758821141034577720465 474569115855775933290349)
              ·
                refine ⟨177963418445915974983881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 474569115855775933290349 177963418445915974983881)
                ·
                  refine ⟨133472563834436981237911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177963418445915974983881 133472563834436981237911)
                  ·
                    rfl

theorem cell20_292429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_292429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292429 prefixEnd_292429 := by exact prefixLift 292429
  have htrace : WordTrace (prefixWord ++ tailWord_292429) baseStart_292429 baseEnd_292429 := by
    simpa [prefixWord, tailWord_292429, baseEnd_292429] using wordTrace_append hprefix tailTrace_292429
  have hstable : (prefixWord ++ tailWord_292429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292429).length < 2 ^ (prefixWord ++ tailWord_292429).sum := by decide
  have hdescent : baseEnd_292429 < baseStart_292429 := by decide
  rcases family_descends (prefixWord ++ tailWord_292429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292430 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_292430 : Nat := 118140960795 + 292430 * 2 ^ 59
def prefixEnd_292430 : Nat := 4983230072969 + 3 ^ 40 * 292430 * 2
def baseEnd_292430 : Nat := 133473020261685422204573

theorem tailTrace_292430 : CollatzResearch.WordTrace tailWord_292430 prefixEnd_292430 133473020261685422204573 := by
  unfold tailWord_292430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1333224791322940989117343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7110532220389018608625829 1333224791322940989117343)
  ·
    refine ⟨1999837186984411483676015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1333224791322940989117343 1999837186984411483676015)
    ·
      refine ⟨2999755780476617225514023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1999837186984411483676015 2999755780476617225514023)
      ·
        refine ⟨4499633670714925838271035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2999755780476617225514023 4499633670714925838271035)
        ·
          refine ⟨6749450506072388757406553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4499633670714925838271035 6749450506072388757406553)
          ·
            refine ⟨5062087879554291568054915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6749450506072388757406553 5062087879554291568054915)
            ·
              refine ⟨7593131819331437352082373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5062087879554291568054915 7593131819331437352082373)
              ·
                refine ⟨1423712216124644503515445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7593131819331437352082373 1423712216124644503515445)
                ·
                  refine ⟨133473020261685422204573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1423712216124644503515445 133473020261685422204573)
                  ·
                    rfl

theorem cell20_292430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_292430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292430 prefixEnd_292430 := by exact prefixLift 292430
  have htrace : WordTrace (prefixWord ++ tailWord_292430) baseStart_292430 baseEnd_292430 := by
    simpa [prefixWord, tailWord_292430, baseEnd_292430] using wordTrace_append hprefix tailTrace_292430
  have hstable : (prefixWord ++ tailWord_292430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292430).length < 2 ^ (prefixWord ++ tailWord_292430).sum := by decide
  have hdescent : baseEnd_292430 < baseStart_292430 := by decide
  rcases family_descends (prefixWord ++ tailWord_292430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292433 : List Nat := [1, 2, 2, 1, 3, 2, 4, 3, 2]
def baseStart_292433 : Nat := 118140960795 + 292433 * 2 ^ 59
def prefixEnd_292433 : Nat := 4983230072969 + 3 ^ 40 * 292433 * 2
def baseEnd_292433 : Nat := 133474389543430745104561

theorem tailTrace_292433 : CollatzResearch.WordTrace tailWord_292433 prefixEnd_292433 133474389543430745104561 := by
  unfold tailWord_292433
  simp only [CollatzResearch.WordTrace]
  refine ⟨10665907749572659425297953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7110605166381772950198635 10665907749572659425297953)
  ·
    refine ⟨7999430812179494568973465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10665907749572659425297953 7999430812179494568973465)
    ·
      refine ⟨5999573109134620926730099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7999430812179494568973465 5999573109134620926730099)
      ·
        refine ⟨8999359663701931390095149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5999573109134620926730099 8999359663701931390095149)
        ·
          refine ⟨3374759873888224271285681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8999359663701931390095149 3374759873888224271285681)
          ·
            refine ⟨2531069905416168203464261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3374759873888224271285681 2531069905416168203464261)
            ·
              refine ⟨474575607265531538149549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2531069905416168203464261 474575607265531538149549)
              ·
                refine ⟨177965852724574326806081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 474575607265531538149549 177965852724574326806081)
                ·
                  refine ⟨133474389543430745104561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 177965852724574326806081 133474389543430745104561)
                  ·
                    rfl

theorem cell20_292433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 2].length) (baseStart_292433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292433 prefixEnd_292433 := by exact prefixLift 292433
  have htrace : WordTrace (prefixWord ++ tailWord_292433) baseStart_292433 baseEnd_292433 := by
    simpa [prefixWord, tailWord_292433, baseEnd_292433] using wordTrace_append hprefix tailTrace_292433
  have hstable : (prefixWord ++ tailWord_292433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292433).length < 2 ^ (prefixWord ++ tailWord_292433).sum := by decide
  have hdescent : baseEnd_292433 < baseStart_292433 := by decide
  rcases family_descends (prefixWord ++ tailWord_292433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292437 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 8]
def baseStart_292437 : Nat := 118140960795 + 292437 * 2 ^ 59
def prefixEnd_292437 : Nat := 4983230072969 + 3 ^ 40 * 292437 * 2
def baseEnd_292437 : Nat := 133476215252424508971211

theorem tailTrace_292437 : CollatzResearch.WordTrace tailWord_292437 prefixEnd_292437 133476215252424508971211 := by
  unfold tailWord_292437
  simp only [CollatzResearch.WordTrace]
  refine ⟨10666053641558168108443565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7110702427705445405629043 10666053641558168108443565)
  ·
    refine ⟨3999770115584313040666337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10666053641558168108443565 3999770115584313040666337)
    ·
      refine ⟨2999827586688234780499753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3999770115584313040666337 2999827586688234780499753)
      ·
        refine ⟨2249870690016176085374815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2999827586688234780499753 2249870690016176085374815)
        ·
          refine ⟨3374806035024264128062223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2249870690016176085374815 3374806035024264128062223)
          ·
            refine ⟨5062209052536396192093335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3374806035024264128062223 5062209052536396192093335)
            ·
              refine ⟨7593313578804594288140003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5062209052536396192093335 7593313578804594288140003)
              ·
                refine ⟨11389970368206891432210005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7593313578804594288140003 11389970368206891432210005)
                ·
                  refine ⟨133476215252424508971211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11389970368206891432210005 133476215252424508971211)
                  ·
                    rfl

theorem cell20_292437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_292437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292437 prefixEnd_292437 := by exact prefixLift 292437
  have htrace : WordTrace (prefixWord ++ tailWord_292437) baseStart_292437 baseEnd_292437 := by
    simpa [prefixWord, tailWord_292437, baseEnd_292437] using wordTrace_append hprefix tailTrace_292437
  have hstable : (prefixWord ++ tailWord_292437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292437).length < 2 ^ (prefixWord ++ tailWord_292437).sum := by decide
  have hdescent : baseEnd_292437 < baseStart_292437 := by decide
  rcases family_descends (prefixWord ++ tailWord_292437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292464 : List Nat := [2, 1, 1, 1, 6, 2, 3, 1, 3]
def baseStart_292464 : Nat := 118140960795 + 292464 * 2 ^ 59
def prefixEnd_292464 : Nat := 4983230072969 + 3 ^ 40 * 292464 * 2
def baseEnd_292464 : Nat := 133488538788132415071101

theorem tailTrace_292464 : CollatzResearch.WordTrace tailWord_292464 prefixEnd_292464 133488538788132415071101 := by
  unfold tailWord_292464
  simp only [CollatzResearch.WordTrace]
  refine ⟨5333519206230175859838223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7111358941640234479784297 5333519206230175859838223)
  ·
    refine ⟨8000278809345263789757335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5333519206230175859838223 8000278809345263789757335)
    ·
      refine ⟨12000418214017895684636003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8000278809345263789757335 12000418214017895684636003)
      ·
        refine ⟨18000627321026843526954005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12000418214017895684636003 18000627321026843526954005)
        ·
          refine ⟨843779405673133290325969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18000627321026843526954005 843779405673133290325969)
          ·
            refine ⟨632834554254849967744477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 843779405673133290325969 632834554254849967744477)
            ·
              refine ⟨237312957845568737904179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 632834554254849967744477 237312957845568737904179)
              ·
                refine ⟨355969436768353106856269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237312957845568737904179 355969436768353106856269)
                ·
                  refine ⟨133488538788132415071101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 355969436768353106856269 133488538788132415071101)
                  ·
                    rfl

theorem cell20_292464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_292464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292464 prefixEnd_292464 := by exact prefixLift 292464
  have htrace : WordTrace (prefixWord ++ tailWord_292464) baseStart_292464 baseEnd_292464 := by
    simpa [prefixWord, tailWord_292464, baseEnd_292464] using wordTrace_append hprefix tailTrace_292464
  have hstable : (prefixWord ++ tailWord_292464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292464).length < 2 ^ (prefixWord ++ tailWord_292464).sum := by decide
  have hdescent : baseEnd_292464 < baseStart_292464 := by decide
  rcases family_descends (prefixWord ++ tailWord_292464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292475 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 4]
def baseStart_292475 : Nat := 118140960795 + 292475 * 2 ^ 59
def prefixEnd_292475 : Nat := 4983230072969 + 3 ^ 40 * 292475 * 2
def baseEnd_292475 : Nat := 133493559487865265704389

theorem tailTrace_292475 : CollatzResearch.WordTrace tailWord_292475 prefixEnd_292475 133493559487865265704389 := by
  unfold tailWord_292475
  simp only [CollatzResearch.WordTrace]
  refine ⟨10667439615420500598326879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7111626410280333732217919 10667439615420500598326879)
  ·
    refine ⟨16001159423130750897490319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10667439615420500598326879 16001159423130750897490319)
    ·
      refine ⟨24001739134696126346235479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16001159423130750897490319 24001739134696126346235479)
      ·
        refine ⟨36002608702044189519353219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24001739134696126346235479 36002608702044189519353219)
        ·
          refine ⟨54003913053066284279029829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36002608702044189519353219 54003913053066284279029829)
          ·
            refine ⟨10125733697449928302318093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54003913053066284279029829 10125733697449928302318093)
            ·
              refine ⟨3797150136543723113369285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10125733697449928302318093 3797150136543723113369285)
              ·
                refine ⟨711965650601948083756741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3797150136543723113369285 711965650601948083756741)
                ·
                  refine ⟨133493559487865265704389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 711965650601948083756741 133493559487865265704389)
                  ·
                    rfl

theorem cell20_292475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_292475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292475 prefixEnd_292475 := by exact prefixLift 292475
  have htrace : WordTrace (prefixWord ++ tailWord_292475) baseStart_292475 baseEnd_292475 := by
    simpa [prefixWord, tailWord_292475, baseEnd_292475] using wordTrace_append hprefix tailTrace_292475
  have hstable : (prefixWord ++ tailWord_292475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292475).length < 2 ^ (prefixWord ++ tailWord_292475).sum := by decide
  have hdescent : baseEnd_292475 < baseStart_292475 := by decide
  rcases family_descends (prefixWord ++ tailWord_292475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292557 : List Nat := [1, 6, 2, 1, 1, 2, 2, 2, 3]
def baseStart_292557 : Nat := 118140960795 + 292557 * 2 ^ 59
def prefixEnd_292557 : Nat := 4983230072969 + 3 ^ 40 * 292557 * 2
def baseEnd_292557 : Nat := 133530986522237424970721

theorem tailTrace_292557 : CollatzResearch.WordTrace tailWord_292557 prefixEnd_292557 133530986522237424970721 := by
  unfold tailWord_292557
  simp only [CollatzResearch.WordTrace]
  refine ⟨10670430401123428602811925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7113620267415619068541283 10670430401123428602811925)
  ·
    refine ⟨500176425052660715756809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 10670430401123428602811925 500176425052660715756809)
    ·
      refine ⟨375132318789495536817607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 500176425052660715756809 375132318789495536817607)
      ·
        refine ⟨562698478184243305226411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375132318789495536817607 562698478184243305226411)
        ·
          refine ⟨844047717276364957839617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562698478184243305226411 844047717276364957839617)
          ·
            refine ⟨633035787957273718379713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 844047717276364957839617 633035787957273718379713)
            ·
              refine ⟨474776840967955288784785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633035787957273718379713 474776840967955288784785)
              ·
                refine ⟨356082630725966466588589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474776840967955288784785 356082630725966466588589)
                ·
                  refine ⟨133530986522237424970721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356082630725966466588589 133530986522237424970721)
                  ·
                    rfl

theorem cell20_292557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_292557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292557 prefixEnd_292557 := by exact prefixLift 292557
  have htrace : WordTrace (prefixWord ++ tailWord_292557) baseStart_292557 baseEnd_292557 := by
    simpa [prefixWord, tailWord_292557, baseEnd_292557] using wordTrace_append hprefix tailTrace_292557
  have hstable : (prefixWord ++ tailWord_292557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292557).length < 2 ^ (prefixWord ++ tailWord_292557).sum := by decide
  have hdescent : baseEnd_292557 < baseStart_292557 := by decide
  rcases family_descends (prefixWord ++ tailWord_292557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292561 : List Nat := [1, 2, 2, 1, 2, 5, 2, 2, 3]
def baseStart_292561 : Nat := 118140960795 + 292561 * 2 ^ 59
def prefixEnd_292561 : Nat := 4983230072969 + 3 ^ 40 * 292561 * 2
def baseEnd_292561 : Nat := 133532812231231188837371

theorem tailTrace_292561 : CollatzResearch.WordTrace tailWord_292561 prefixEnd_292561 133532812231231188837371 := by
  unfold tailWord_292561
  simp only [CollatzResearch.WordTrace]
  refine ⟨10670576293108937285957537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7113717528739291523971691 10670576293108937285957537)
  ·
    refine ⟨8002932219831702964468153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10670576293108937285957537 8002932219831702964468153)
    ·
      refine ⟨6002199164873777223351115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8002932219831702964468153 6002199164873777223351115)
      ·
        refine ⟨9003298747310665835026673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6002199164873777223351115 9003298747310665835026673)
        ·
          refine ⟨6752474060482999376270005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9003298747310665835026673 6752474060482999376270005)
          ·
            refine ⟨633044443170281191525313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6752474060482999376270005 633044443170281191525313)
            ·
              refine ⟨474783332377710893643985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633044443170281191525313 474783332377710893643985)
              ·
                refine ⟨356087499283283170232989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474783332377710893643985 356087499283283170232989)
                ·
                  refine ⟨133532812231231188837371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356087499283283170232989 133532812231231188837371)
                  ·
                    rfl

theorem cell20_292561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_292561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292561 prefixEnd_292561 := by exact prefixLift 292561
  have htrace : WordTrace (prefixWord ++ tailWord_292561) baseStart_292561 baseEnd_292561 := by
    simpa [prefixWord, tailWord_292561, baseEnd_292561] using wordTrace_append hprefix tailTrace_292561
  have hstable : (prefixWord ++ tailWord_292561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292561).length < 2 ^ (prefixWord ++ tailWord_292561).sum := by decide
  have hdescent : baseEnd_292561 < baseStart_292561 := by decide
  rcases family_descends (prefixWord ++ tailWord_292561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292564 : List Nat := [2, 4, 1, 3, 1, 2, 1, 4, 2]
def baseStart_292564 : Nat := 118140960795 + 292564 * 2 ^ 59
def prefixEnd_292564 : Nat := 4983230072969 + 3 ^ 40 * 292564 * 2
def baseEnd_292564 : Nat := 133534181512976511737359

theorem tailTrace_292564 : CollatzResearch.WordTrace tailWord_292564 prefixEnd_292564 133534181512976511737359 := by
  unfold tailWord_292564
  simp only [CollatzResearch.WordTrace]
  refine ⟨5335342856049034399158373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7113790474732045865544497 5335342856049034399158373)
  ·
    refine ⟨1000376785509193949842195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5335342856049034399158373 1000376785509193949842195)
    ·
      refine ⟨1500565178263790924763293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1000376785509193949842195 1500565178263790924763293)
      ·
        refine ⟨562711941848921596786235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1500565178263790924763293 562711941848921596786235)
        ·
          refine ⟨844067912773382395179353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562711941848921596786235 844067912773382395179353)
          ·
            refine ⟨633050934580036796384515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 844067912773382395179353 633050934580036796384515)
            ·
              refine ⟨949576401870055194576773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633050934580036796384515 949576401870055194576773)
              ·
                refine ⟨178045575350635348983145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 949576401870055194576773 178045575350635348983145)
                ·
                  refine ⟨133534181512976511737359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178045575350635348983145 133534181512976511737359)
                  ·
                    rfl

theorem cell20_292564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_292564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292564 prefixEnd_292564 := by exact prefixLift 292564
  have htrace : WordTrace (prefixWord ++ tailWord_292564) baseStart_292564 baseEnd_292564 := by
    simpa [prefixWord, tailWord_292564, baseEnd_292564] using wordTrace_append hprefix tailTrace_292564
  have hstable : (prefixWord ++ tailWord_292564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292564).length < 2 ^ (prefixWord ++ tailWord_292564).sum := by decide
  have hdescent : baseEnd_292564 < baseStart_292564 := by decide
  rcases family_descends (prefixWord ++ tailWord_292564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292644 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 4]
def baseStart_292644 : Nat := 118140960795 + 292644 * 2 ^ 59
def prefixEnd_292644 : Nat := 4983230072969 + 3 ^ 40 * 292644 * 2
def baseEnd_292644 : Nat := 133570695692851789070365

theorem tailTrace_292644 : CollatzResearch.WordTrace tailWord_292644 prefixEnd_292644 133570695692851789070365 := by
  unfold tailWord_292644
  simp only [CollatzResearch.WordTrace]
  refine ⟨5336801775904121230614493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7115735701205494974152657 5336801775904121230614493)
  ·
    refine ⟨2001300665964045461480435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5336801775904121230614493 2001300665964045461480435)
    ·
      refine ⟨3001950998946068192220653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2001300665964045461480435 3001950998946068192220653)
      ·
        refine ⟨1125731624604775572082745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3001950998946068192220653 1125731624604775572082745)
        ·
          refine ⟨844298718453581679062059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1125731624604775572082745 844298718453581679062059)
          ·
            refine ⟨1266448077680372518593089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844298718453581679062059 1266448077680372518593089)
            ·
              refine ⟨949836058260279388944817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1266448077680372518593089 949836058260279388944817)
              ·
                refine ⟨712377043695209541708613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 949836058260279388944817 712377043695209541708613)
                ·
                  refine ⟨133570695692851789070365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 712377043695209541708613 133570695692851789070365)
                  ·
                    rfl

theorem cell20_292644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_292644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292644 prefixEnd_292644 := by exact prefixLift 292644
  have htrace : WordTrace (prefixWord ++ tailWord_292644) baseStart_292644 baseEnd_292644 := by
    simpa [prefixWord, tailWord_292644, baseEnd_292644] using wordTrace_append hprefix tailTrace_292644
  have hstable : (prefixWord ++ tailWord_292644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292644).length < 2 ^ (prefixWord ++ tailWord_292644).sum := by decide
  have hdescent : baseEnd_292644 < baseStart_292644 := by decide
  rcases family_descends (prefixWord ++ tailWord_292644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292658 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_292658 : Nat := 118140960795 + 292658 * 2 ^ 59
def prefixEnd_292658 : Nat := 4983230072969 + 3 ^ 40 * 292658 * 2
def baseEnd_292658 : Nat := 133577085674329962603641

theorem tailTrace_292658 : CollatzResearch.WordTrace tailWord_292658 prefixEnd_292658 133577085674329962603641 := by
  unfold tailWord_292658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2668528543439380713059657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7116076115838348568159085 2668528543439380713059657)
  ·
    refine ⟨2001396407579535534794743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2668528543439380713059657 2001396407579535534794743)
    ·
      refine ⟨3002094611369303302192115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2001396407579535534794743 3002094611369303302192115)
      ·
        refine ⟨4503141917053954953288173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3002094611369303302192115 4503141917053954953288173)
        ·
          refine ⟨1688678218895233107483065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4503141917053954953288173 1688678218895233107483065)
          ·
            refine ⟨1266508664171424830612299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1688678218895233107483065 1266508664171424830612299)
            ·
              refine ⟨1899762996257137245918449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1266508664171424830612299 1899762996257137245918449)
              ·
                refine ⟨1424822247192852934438837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1899762996257137245918449 1424822247192852934438837)
                ·
                  refine ⟨133577085674329962603641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1424822247192852934438837 133577085674329962603641)
                  ·
                    rfl

theorem cell20_292658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_292658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292658 prefixEnd_292658 := by exact prefixLift 292658
  have htrace : WordTrace (prefixWord ++ tailWord_292658) baseStart_292658 baseEnd_292658 := by
    simpa [prefixWord, tailWord_292658, baseEnd_292658] using wordTrace_append hprefix tailTrace_292658
  have hstable : (prefixWord ++ tailWord_292658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292658).length < 2 ^ (prefixWord ++ tailWord_292658).sum := by decide
  have hdescent : baseEnd_292658 < baseStart_292658 := by decide
  rcases family_descends (prefixWord ++ tailWord_292658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292678 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_292678 : Nat := 118140960795 + 292678 * 2 ^ 59
def prefixEnd_292678 : Nat := 4983230072969 + 3 ^ 40 * 292678 * 2
def baseEnd_292678 : Nat := 133586214219298781936893

theorem tailTrace_292678 : CollatzResearch.WordTrace tailWord_292678 prefixEnd_292678 133586214219298781936893 := by
  unfold tailWord_292678
  simp only [CollatzResearch.WordTrace]
  refine ⟨333588863552658320873959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7116562422456710845311125 333588863552658320873959)
  ·
    refine ⟨500383295328987481310939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 333588863552658320873959 500383295328987481310939)
    ·
      refine ⟨750574942993481221966409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 500383295328987481310939 750574942993481221966409)
      ·
        refine ⟨562931207245110916474807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 750574942993481221966409 562931207245110916474807)
        ·
          refine ⟨844396810867666374712211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562931207245110916474807 844396810867666374712211)
          ·
            refine ⟨1266595216301499562068317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844396810867666374712211 1266595216301499562068317)
            ·
              refine ⟨474973206113062335775619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1266595216301499562068317 474973206113062335775619)
              ·
                refine ⟨712459809169593503663429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 474973206113062335775619 712459809169593503663429)
                ·
                  refine ⟨133586214219298781936893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 712459809169593503663429 133586214219298781936893)
                  ·
                    rfl

theorem cell20_292678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_292678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292678 prefixEnd_292678 := by exact prefixLift 292678
  have htrace : WordTrace (prefixWord ++ tailWord_292678) baseStart_292678 baseEnd_292678 := by
    simpa [prefixWord, tailWord_292678, baseEnd_292678] using wordTrace_append hprefix tailTrace_292678
  have hstable : (prefixWord ++ tailWord_292678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292678).length < 2 ^ (prefixWord ++ tailWord_292678).sum := by decide
  have hdescent : baseEnd_292678 < baseStart_292678 := by decide
  rcases family_descends (prefixWord ++ tailWord_292678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292689 : List Nat := [1, 2, 2, 1, 5, 2, 2, 5]
def baseStart_292689 : Nat := 118140960795 + 292689 * 2 ^ 59
def prefixEnd_292689 : Nat := 4983230072969 + 3 ^ 40 * 292689 * 2
def baseEnd_292689 : Nat := 44530411639677210856727

theorem tailTrace_292689 : CollatzResearch.WordTrace tailWord_292689 prefixEnd_292689 44530411639677210856727 := by
  unfold tailWord_292689
  simp only [CollatzResearch.WordTrace]
  refine ⟨10675244836645215146617121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7116829891096810097744747 10675244836645215146617121)
  ·
    refine ⟨8006433627483911359962841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10675244836645215146617121 8006433627483911359962841)
    ·
      refine ⟨6004825220612933519972131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8006433627483911359962841 6004825220612933519972131)
      ·
        refine ⟨9007237830919400279958197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6004825220612933519972131 9007237830919400279958197)
        ·
          refine ⟨844428546648693776246081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9007237830919400279958197 844428546648693776246081)
          ·
            refine ⟨633321409986520332184561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 844428546648693776246081 633321409986520332184561)
            ·
              refine ⟨474991057489890249138421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 633321409986520332184561 474991057489890249138421)
              ·
                refine ⟨44530411639677210856727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 474991057489890249138421 44530411639677210856727)
                ·
                  rfl

theorem cell20_292689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 5].length) (baseStart_292689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292689 prefixEnd_292689 := by exact prefixLift 292689
  have htrace : WordTrace (prefixWord ++ tailWord_292689) baseStart_292689 baseEnd_292689 := by
    simpa [prefixWord, tailWord_292689, baseEnd_292689] using wordTrace_append hprefix tailTrace_292689
  have hstable : (prefixWord ++ tailWord_292689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292689).length < 2 ^ (prefixWord ++ tailWord_292689).sum := by decide
  have hdescent : baseEnd_292689 < baseStart_292689 := by decide
  rcases family_descends (prefixWord ++ tailWord_292689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292692 : List Nat := [2, 4, 1, 1, 3, 1, 4, 1, 3]
def baseStart_292692 : Nat := 118140960795 + 292692 * 2 ^ 59
def prefixEnd_292692 : Nat := 4983230072969 + 3 ^ 40 * 292692 * 2
def baseEnd_292692 : Nat := 133592604200776955470169

theorem tailTrace_292692 : CollatzResearch.WordTrace tailWord_292692 prefixEnd_292692 133592604200776955470169 := by
  unfold tailWord_292692
  simp only [CollatzResearch.WordTrace]
  refine ⟨5337677127817173329488165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7116902837089564439317553 5337677127817173329488165)
  ·
    refine ⟨1000814461465719999279031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5337677127817173329488165 1000814461465719999279031)
    ·
      refine ⟨1501221692198579998918547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1000814461465719999279031 1501221692198579998918547)
      ·
        refine ⟨2251832538297869998377821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1501221692198579998918547 2251832538297869998377821)
        ·
          refine ⟨844437201861701249391683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2251832538297869998377821 844437201861701249391683)
          ·
            refine ⟨1266655802792551874087525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844437201861701249391683 1266655802792551874087525)
            ·
              refine ⟨237497963023603476391411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1266655802792551874087525 237497963023603476391411)
              ·
                refine ⟨356246944535405214587117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237497963023603476391411 356246944535405214587117)
                ·
                  refine ⟨133592604200776955470169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356246944535405214587117 133592604200776955470169)
                  ·
                    rfl

theorem cell20_292692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_292692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292692 prefixEnd_292692 := by exact prefixLift 292692
  have htrace : WordTrace (prefixWord ++ tailWord_292692) baseStart_292692 baseEnd_292692 := by
    simpa [prefixWord, tailWord_292692, baseEnd_292692] using wordTrace_append hprefix tailTrace_292692
  have hstable : (prefixWord ++ tailWord_292692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292692).length < 2 ^ (prefixWord ++ tailWord_292692).sum := by decide
  have hdescent : baseEnd_292692 < baseStart_292692 := by decide
  rcases family_descends (prefixWord ++ tailWord_292692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292720 : List Nat := [2, 1, 1, 1, 4, 1, 1, 7, 2]
def baseStart_292720 : Nat := 118140960795 + 292720 * 2 ^ 59
def prefixEnd_292720 : Nat := 4983230072969 + 3 ^ 40 * 292720 * 2
def baseEnd_292720 : Nat := 133605384163733302536721

theorem tailTrace_292720 : CollatzResearch.WordTrace tailWord_292720 prefixEnd_292720 133605384163733302536721 := by
  unfold tailWord_292720
  simp only [CollatzResearch.WordTrace]
  refine ⟨5338187749766453720497807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7117583666355271627330409 5338187749766453720497807)
  ·
    refine ⟨8007281624649680580746711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5338187749766453720497807 8007281624649680580746711)
    ·
      refine ⟨12010922436974520871120067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8007281624649680580746711 12010922436974520871120067)
      ·
        refine ⟨18016383655461781306680101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12010922436974520871120067 18016383655461781306680101)
        ·
          refine ⟨3378071935399083995002519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18016383655461781306680101 3378071935399083995002519)
          ·
            refine ⟨5067107903098625992503779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3378071935399083995002519 5067107903098625992503779)
            ·
              refine ⟨7600661854647938988755669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5067107903098625992503779 7600661854647938988755669)
              ·
                refine ⟨178140512218311070048961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7600661854647938988755669 178140512218311070048961)
                ·
                  refine ⟨133605384163733302536721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178140512218311070048961 133605384163733302536721)
                  ·
                    rfl

theorem cell20_292720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 2].length) (baseStart_292720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292720 prefixEnd_292720 := by exact prefixLift 292720
  have htrace : WordTrace (prefixWord ++ tailWord_292720) baseStart_292720 baseEnd_292720 := by
    simpa [prefixWord, tailWord_292720, baseEnd_292720] using wordTrace_append hprefix tailTrace_292720
  have hstable : (prefixWord ++ tailWord_292720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292720).length < 2 ^ (prefixWord ++ tailWord_292720).sum := by decide
  have hdescent : baseEnd_292720 < baseStart_292720 := by decide
  rcases family_descends (prefixWord ++ tailWord_292720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292741 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 4]
def baseStart_292741 : Nat := 118140960795 + 292741 * 2 ^ 59
def prefixEnd_292741 : Nat := 4983230072969 + 3 ^ 40 * 292741 * 2
def baseEnd_292741 : Nat := 133614969135950562836635

theorem tailTrace_292741 : CollatzResearch.WordTrace tailWord_292741 prefixEnd_292741 133614969135950562836635 := by
  unfold tailWord_292741
  simp only [CollatzResearch.WordTrace]
  refine ⟨10677141432456828027510077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7118094288304552018340051 10677141432456828027510077)
  ·
    refine ⟨4003928037171310510316279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10677141432456828027510077 4003928037171310510316279)
    ·
      refine ⟨6005892055756965765474419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4003928037171310510316279 6005892055756965765474419)
      ·
        refine ⟨9008838083635448648211629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6005892055756965765474419 9008838083635448648211629)
        ·
          refine ⟨3378314281363293243079361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9008838083635448648211629 3378314281363293243079361)
          ·
            refine ⟨2533735711022469932309521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3378314281363293243079361 2533735711022469932309521)
            ·
              refine ⟨1900301783266852449232141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2533735711022469932309521 1900301783266852449232141)
              ·
                refine ⟨712613168725069668462053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1900301783266852449232141 712613168725069668462053)
                ·
                  refine ⟨133614969135950562836635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 712613168725069668462053 133614969135950562836635)
                  ·
                    rfl

theorem cell20_292741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_292741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292741 prefixEnd_292741 := by exact prefixLift 292741
  have htrace : WordTrace (prefixWord ++ tailWord_292741) baseStart_292741 baseEnd_292741 := by
    simpa [prefixWord, tailWord_292741, baseEnd_292741] using wordTrace_append hprefix tailTrace_292741
  have hstable : (prefixWord ++ tailWord_292741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292741).length < 2 ^ (prefixWord ++ tailWord_292741).sum := by decide
  have hdescent : baseEnd_292741 < baseStart_292741 := by decide
  rcases family_descends (prefixWord ++ tailWord_292741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292744 : List Nat := [2, 1, 3, 3, 3, 2, 1, 5]
def baseStart_292744 : Nat := 118140960795 + 292744 * 2 ^ 59
def prefixEnd_292744 : Nat := 4983230072969 + 3 ^ 40 * 292744 * 2
def baseEnd_292744 : Nat := 44538779472565295245541

theorem tailTrace_292744 : CollatzResearch.WordTrace tailWord_292744 prefixEnd_292744 44538779472565295245541 := by
  unfold tailWord_292744
  simp only [CollatzResearch.WordTrace]
  refine ⟨5338625425722979769934643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7118167234297306359912857 5338625425722979769934643)
  ·
    refine ⟨8007938138584469654901965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5338625425722979769934643 8007938138584469654901965)
    ·
      refine ⟨3002976801969176120588237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8007938138584469654901965 3002976801969176120588237)
      ·
        refine ⟨1126116300738441045220589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3002976801969176120588237 1126116300738441045220589)
        ·
          refine ⟨422293612776915391957721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1126116300738441045220589 422293612776915391957721)
          ·
            refine ⟨316720209582686543968291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422293612776915391957721 316720209582686543968291)
            ·
              refine ⟨475080314374029815952437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316720209582686543968291 475080314374029815952437)
              ·
                refine ⟨44538779472565295245541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 475080314374029815952437 44538779472565295245541)
                ·
                  rfl

theorem cell20_292744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_292744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292744 prefixEnd_292744 := by exact prefixLift 292744
  have htrace : WordTrace (prefixWord ++ tailWord_292744) baseStart_292744 baseEnd_292744 := by
    simpa [prefixWord, tailWord_292744, baseEnd_292744] using wordTrace_append hprefix tailTrace_292744
  have hstable : (prefixWord ++ tailWord_292744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292744).length < 2 ^ (prefixWord ++ tailWord_292744).sum := by decide
  have hdescent : baseEnd_292744 < baseStart_292744 := by decide
  rcases family_descends (prefixWord ++ tailWord_292744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292775 : List Nat := [1, 1, 6, 1, 2, 1, 1, 5, 2]
def baseStart_292775 : Nat := 118140960795 + 292775 * 2 ^ 59
def prefixEnd_292775 : Nat := 4983230072969 + 3 ^ 40 * 292775 * 2
def baseEnd_292775 : Nat := 133630487662397555703163

theorem tailTrace_292775 : CollatzResearch.WordTrace tailWord_292775 prefixEnd_292775 133630487662397555703163 := by
  unfold tailWord_292775
  simp only [CollatzResearch.WordTrace]
  refine ⟨10678381514333651834247779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7118921009555767889498519 10678381514333651834247779)
  ·
    refine ⟨16017572271500477751371669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10678381514333651834247779 16017572271500477751371669)
    ·
      refine ⟨750823700226584894595547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16017572271500477751371669 750823700226584894595547)
      ·
        refine ⟨1126235550339877341893321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 750823700226584894595547 1126235550339877341893321)
        ·
          refine ⟨844676662754908006419991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1126235550339877341893321 844676662754908006419991)
          ·
            refine ⟨1267014994132362009629987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 844676662754908006419991 1267014994132362009629987)
            ·
              refine ⟨1900522491198543014444981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267014994132362009629987 1900522491198543014444981)
              ·
                refine ⟨178173983549863407604217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1900522491198543014444981 178173983549863407604217)
                ·
                  refine ⟨133630487662397555703163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178173983549863407604217 133630487662397555703163)
                  ·
                    rfl

theorem cell20_292775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 2].length) (baseStart_292775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292775 prefixEnd_292775 := by exact prefixLift 292775
  have htrace : WordTrace (prefixWord ++ tailWord_292775) baseStart_292775 baseEnd_292775 := by
    simpa [prefixWord, tailWord_292775, baseEnd_292775] using wordTrace_append hprefix tailTrace_292775
  have hstable : (prefixWord ++ tailWord_292775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292775).length < 2 ^ (prefixWord ++ tailWord_292775).sum := by decide
  have hdescent : baseEnd_292775 < baseStart_292775 := by decide
  rcases family_descends (prefixWord ++ tailWord_292775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292789 : List Nat := [1, 3, 3, 2, 1, 2, 3, 2, 3]
def baseStart_292789 : Nat := 118140960795 + 292789 * 2 ^ 59
def prefixEnd_292789 : Nat := 4983230072969 + 3 ^ 40 * 292789 * 2
def baseEnd_292789 : Nat := 133636877643875729236439

theorem tailTrace_292789 : CollatzResearch.WordTrace tailWord_292789 prefixEnd_292789 133636877643875729236439 := by
  unfold tailWord_292789
  simp only [CollatzResearch.WordTrace]
  refine ⟨10678892136282932225257421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7119261424188621483504947 10678892136282932225257421)
  ·
    refine ⟨4004584551106099584471533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10678892136282932225257421 4004584551106099584471533)
    ·
      refine ⟨1501719206664787344176825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4004584551106099584471533 1501719206664787344176825)
      ·
        refine ⟨1126289404998590508132619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1501719206664787344176825 1126289404998590508132619)
        ·
          refine ⟨1689434107497885762198929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1126289404998590508132619 1689434107497885762198929)
          ·
            refine ⟨1267075580623414321649197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1689434107497885762198929 1267075580623414321649197)
            ·
              refine ⟨475153342733780370618449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1267075580623414321649197 475153342733780370618449)
              ·
                refine ⟨356365007050335277963837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 475153342733780370618449 356365007050335277963837)
                ·
                  refine ⟨133636877643875729236439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356365007050335277963837 133636877643875729236439)
                  ·
                    rfl

theorem cell20_292789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_292789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292789 prefixEnd_292789 := by exact prefixLift 292789
  have htrace : WordTrace (prefixWord ++ tailWord_292789) baseStart_292789 baseEnd_292789 := by
    simpa [prefixWord, tailWord_292789, baseEnd_292789] using wordTrace_append hprefix tailTrace_292789
  have hstable : (prefixWord ++ tailWord_292789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292789).length < 2 ^ (prefixWord ++ tailWord_292789).sum := by decide
  have hdescent : baseEnd_292789 < baseStart_292789 := by decide
  rcases family_descends (prefixWord ++ tailWord_292789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292810 : List Nat := [3, 1, 2, 1, 2, 1, 2, 5, 3]
def baseStart_292810 : Nat := 118140960795 + 292810 * 2 ^ 59
def prefixEnd_292810 : Nat := 4983230072969 + 3 ^ 40 * 292810 * 2
def baseEnd_292810 : Nat := 133646462616092989536353

theorem tailTrace_292810 : CollatzResearch.WordTrace tailWord_292810 prefixEnd_292810 133646462616092989536353 := by
  unfold tailWord_292810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2669914517301713202942971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7119772046137901874514589 2669914517301713202942971)
  ·
    refine ⟨4004871775952569804414457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2669914517301713202942971 4004871775952569804414457)
    ·
      refine ⟨3003653831964427353310843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4004871775952569804414457 3003653831964427353310843)
      ·
        refine ⟨4505480747946641029966265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3003653831964427353310843 4505480747946641029966265)
        ·
          refine ⟨3379110560959980772474699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4505480747946641029966265 3379110560959980772474699)
          ·
            refine ⟨5068665841439971158712049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3379110560959980772474699 5068665841439971158712049)
            ·
              refine ⟨3801499381079978369034037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5068665841439971158712049 3801499381079978369034037)
              ·
                refine ⟨356390566976247972096941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3801499381079978369034037 356390566976247972096941)
                ·
                  refine ⟨133646462616092989536353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356390566976247972096941 133646462616092989536353)
                  ·
                    rfl

theorem cell20_292810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_292810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292810 prefixEnd_292810 := by exact prefixLift 292810
  have htrace : WordTrace (prefixWord ++ tailWord_292810) baseStart_292810 baseEnd_292810 := by
    simpa [prefixWord, tailWord_292810, baseEnd_292810] using wordTrace_append hprefix tailTrace_292810
  have hstable : (prefixWord ++ tailWord_292810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292810).length < 2 ^ (prefixWord ++ tailWord_292810).sum := by decide
  have hdescent : baseEnd_292810 < baseStart_292810 := by decide
  rcases family_descends (prefixWord ++ tailWord_292810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292824 : List Nat := [2, 1, 2, 2, 2, 2, 3, 6]
def baseStart_292824 : Nat := 118140960795 + 292824 * 2 ^ 59
def prefixEnd_292824 : Nat := 4983230072969 + 3 ^ 40 * 292824 * 2
def baseEnd_292824 : Nat := 44550950865857054356543

theorem tailTrace_292824 : CollatzResearch.WordTrace tailWord_292824 prefixEnd_292824 44550950865857054356543 := by
  unfold tailWord_292824
  simp only [CollatzResearch.WordTrace]
  refine ⟨5340084345578066601390763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7120112460770755468521017 5340084345578066601390763)
  ·
    refine ⟨8010126518367099902086145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5340084345578066601390763 8010126518367099902086145)
    ·
      refine ⟨6007594888775324926564609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8010126518367099902086145 6007594888775324926564609)
      ·
        refine ⟨4505696166581493694923457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6007594888775324926564609 4505696166581493694923457)
        ·
          refine ⟨3379272124936120271192593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4505696166581493694923457 3379272124936120271192593)
          ·
            refine ⟨2534454093702090203394445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3379272124936120271192593 2534454093702090203394445)
            ·
              refine ⟨950420285138283826272917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2534454093702090203394445 950420285138283826272917)
              ·
                refine ⟨44550950865857054356543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 950420285138283826272917 44550950865857054356543)
                ·
                  rfl

theorem cell20_292824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_292824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292824 prefixEnd_292824 := by exact prefixLift 292824
  have htrace : WordTrace (prefixWord ++ tailWord_292824) baseStart_292824 baseEnd_292824 := by
    simpa [prefixWord, tailWord_292824, baseEnd_292824] using wordTrace_append hprefix tailTrace_292824
  have hstable : (prefixWord ++ tailWord_292824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292824).length < 2 ^ (prefixWord ++ tailWord_292824).sum := by decide
  have hdescent : baseEnd_292824 < baseStart_292824 := by decide
  rcases family_descends (prefixWord ++ tailWord_292824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292900 : List Nat := [2, 3, 1, 4, 10]
def baseStart_292900 : Nat := 118140960795 + 292900 * 2 ^ 59
def prefixEnd_292900 : Nat := 4983230072969 + 3 ^ 40 * 292900 * 2
def baseEnd_292900 : Nat := 1650463469980897241185

theorem tailTrace_292900 : CollatzResearch.WordTrace tailWord_292900 prefixEnd_292900 1650463469980897241185 := by
  unfold tailWord_292900
  simp only [CollatzResearch.WordTrace]
  refine ⟨5341470319440399091274077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7121960425920532121698769 5341470319440399091274077)
  ·
    refine ⟨2003051369790149659227779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5341470319440399091274077 2003051369790149659227779)
    ·
      refine ⟨3004577054685224488841669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2003051369790149659227779 3004577054685224488841669)
      ·
        refine ⟨563358197753479591657813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3004577054685224488841669 563358197753479591657813)
        ·
          refine ⟨1650463469980897241185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 563358197753479591657813 1650463469980897241185)
          ·
            rfl

theorem cell20_292900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 10].length) (baseStart_292900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292900 prefixEnd_292900 := by exact prefixLift 292900
  have htrace : WordTrace (prefixWord ++ tailWord_292900) baseStart_292900 baseEnd_292900 := by
    simpa [prefixWord, tailWord_292900, baseEnd_292900] using wordTrace_append hprefix tailTrace_292900
  have hstable : (prefixWord ++ tailWord_292900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292900).length < 2 ^ (prefixWord ++ tailWord_292900).sum := by decide
  have hdescent : baseEnd_292900 < baseStart_292900 := by decide
  rcases family_descends (prefixWord ++ tailWord_292900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292906 : List Nat := [3, 1, 4, 1, 2, 1, 4, 2, 2]
def baseStart_292906 : Nat := 118140960795 + 292906 * 2 ^ 59
def prefixEnd_292906 : Nat := 4983230072969 + 3 ^ 40 * 292906 * 2
def baseEnd_292906 : Nat := 133690279631943322335961

theorem tailTrace_292906 : CollatzResearch.WordTrace tailWord_292906 prefixEnd_292906 133690279631943322335961 := by
  unfold tailWord_292906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2670789869214765301816643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7122106317906040804844381 2670789869214765301816643)
  ·
    refine ⟨4006184803822147952724965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2670789869214765301816643 4006184803822147952724965)
    ·
      refine ⟨751159650716652741135931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4006184803822147952724965 751159650716652741135931)
      ·
        refine ⟨1126739476074979111703897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751159650716652741135931 1126739476074979111703897)
        ·
          refine ⟨845054607056234333777923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1126739476074979111703897 845054607056234333777923)
          ·
            refine ⟨1267581910584351500666885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845054607056234333777923 1267581910584351500666885)
            ·
              refine ⟨237671608234565906375041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1267581910584351500666885 237671608234565906375041)
              ·
                refine ⟨178253706175924429781281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 237671608234565906375041 178253706175924429781281)
                ·
                  refine ⟨133690279631943322335961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178253706175924429781281 133690279631943322335961)
                  ·
                    rfl

theorem cell20_292906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_292906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292906 prefixEnd_292906 := by exact prefixLift 292906
  have htrace : WordTrace (prefixWord ++ tailWord_292906) baseStart_292906 baseEnd_292906 := by
    simpa [prefixWord, tailWord_292906, baseEnd_292906] using wordTrace_append hprefix tailTrace_292906
  have hstable : (prefixWord ++ tailWord_292906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292906).length < 2 ^ (prefixWord ++ tailWord_292906).sum := by decide
  have hdescent : baseEnd_292906 < baseStart_292906 := by decide
  rcases family_descends (prefixWord ++ tailWord_292906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292924 : List Nat := [2, 2, 2, 2, 2, 1, 1, 5, 3]
def baseStart_292924 : Nat := 118140960795 + 292924 * 2 ^ 59
def prefixEnd_292924 : Nat := 4983230072969 + 3 ^ 40 * 292924 * 2
def baseEnd_292924 : Nat := 133698495322415259735887

theorem tailTrace_292924 : CollatzResearch.WordTrace tailWord_292924 prefixEnd_292924 133698495322415259735887 := by
  unfold tailWord_292924
  simp only [CollatzResearch.WordTrace]
  refine ⟨5341907995396925140710913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7122543993862566854281217 5341907995396925140710913)
  ·
    refine ⟨4006430996547693855533185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5341907995396925140710913 4006430996547693855533185)
    ·
      refine ⟨3004823247410770391649889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4006430996547693855533185 3004823247410770391649889)
      ·
        refine ⟨2253617435558077793737417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3004823247410770391649889 2253617435558077793737417)
        ·
          refine ⟨1690213076668558345303063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2253617435558077793737417 1690213076668558345303063)
          ·
            refine ⟨2535319615002837517954595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1690213076668558345303063 2535319615002837517954595)
            ·
              refine ⟨3802979422504256276931893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2535319615002837517954595 3802979422504256276931893)
              ·
                refine ⟨356529320859774025962365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3802979422504256276931893 356529320859774025962365)
                ·
                  refine ⟨133698495322415259735887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356529320859774025962365 133698495322415259735887)
                  ·
                    rfl

theorem cell20_292924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_292924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292924 prefixEnd_292924 := by exact prefixLift 292924
  have htrace : WordTrace (prefixWord ++ tailWord_292924) baseStart_292924 baseEnd_292924 := by
    simpa [prefixWord, tailWord_292924, baseEnd_292924] using wordTrace_append hprefix tailTrace_292924
  have hstable : (prefixWord ++ tailWord_292924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292924).length < 2 ^ (prefixWord ++ tailWord_292924).sum := by decide
  have hdescent : baseEnd_292924 < baseStart_292924 := by decide
  rcases family_descends (prefixWord ++ tailWord_292924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292945 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 5]
def baseStart_292945 : Nat := 118140960795 + 292945 * 2 ^ 59
def prefixEnd_292945 : Nat := 4983230072969 + 3 ^ 40 * 292945 * 2
def baseEnd_292945 : Nat := 133708080294632520035801

theorem tailTrace_292945 : CollatzResearch.WordTrace tailWord_292945 prefixEnd_292945 133708080294632520035801 := by
  unfold tailWord_292945
  simp only [CollatzResearch.WordTrace]
  refine ⟨10684581923717770867936289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7123054615811847245290859 10684581923717770867936289)
  ·
    refine ⟨8013436442788328150952217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10684581923717770867936289 8013436442788328150952217)
    ·
      refine ⟨6010077332091246113214163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8013436442788328150952217 6010077332091246113214163)
      ·
        refine ⟨9015115998136869169821245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6010077332091246113214163 9015115998136869169821245)
        ·
          refine ⟨3380668499301325938682967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9015115998136869169821245 3380668499301325938682967)
          ·
            refine ⟨5071002748951988908024451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3380668499301325938682967 5071002748951988908024451)
            ·
              refine ⟨7606504123427983362036677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5071002748951988908024451 7606504123427983362036677)
              ·
                refine ⟨1426219523142746880381877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7606504123427983362036677 1426219523142746880381877)
                ·
                  refine ⟨133708080294632520035801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1426219523142746880381877 133708080294632520035801)
                  ·
                    rfl

theorem cell20_292945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_292945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292945 prefixEnd_292945 := by exact prefixLift 292945
  have htrace : WordTrace (prefixWord ++ tailWord_292945) baseStart_292945 baseEnd_292945 := by
    simpa [prefixWord, tailWord_292945, baseEnd_292945] using wordTrace_append hprefix tailTrace_292945
  have hstable : (prefixWord ++ tailWord_292945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292945).length < 2 ^ (prefixWord ++ tailWord_292945).sum := by decide
  have hdescent : baseEnd_292945 < baseStart_292945 := by decide
  rcases family_descends (prefixWord ++ tailWord_292945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292969 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 4]
def baseStart_292969 : Nat := 118140960795 + 292969 * 2 ^ 59
def prefixEnd_292969 : Nat := 4983230072969 + 3 ^ 40 * 292969 * 2
def baseEnd_292969 : Nat := 133719034548595103235703

theorem tailTrace_292969 : CollatzResearch.WordTrace tailWord_292969 prefixEnd_292969 133719034548595103235703 := by
  unfold tailWord_292969
  simp only [CollatzResearch.WordTrace]
  refine ⟨10685457275630822966809961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7123638183753881977873307 10685457275630822966809961)
  ·
    refine ⟨8014092956723117225107471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10685457275630822966809961 8014092956723117225107471)
    ·
      refine ⟨12021139435084675837661207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8014092956723117225107471 12021139435084675837661207)
      ·
        refine ⟨18031709152627013756491811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12021139435084675837661207 18031709152627013756491811)
        ·
          refine ⟨27047563728940520634737717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18031709152627013756491811 27047563728940520634737717)
          ·
            refine ⟨2535709099588173809506661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27047563728940520634737717 2535709099588173809506661)
            ·
              refine ⟨475445456172782589282499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2535709099588173809506661 475445456172782589282499)
              ·
                refine ⟨713168184259173883923749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 475445456172782589282499 713168184259173883923749)
                ·
                  refine ⟨133719034548595103235703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 713168184259173883923749 133719034548595103235703)
                  ·
                    rfl

theorem cell20_292969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_292969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292969 prefixEnd_292969 := by exact prefixLift 292969
  have htrace : WordTrace (prefixWord ++ tailWord_292969) baseStart_292969 baseEnd_292969 := by
    simpa [prefixWord, tailWord_292969, baseEnd_292969] using wordTrace_append hprefix tailTrace_292969
  have hstable : (prefixWord ++ tailWord_292969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292969).length < 2 ^ (prefixWord ++ tailWord_292969).sum := by decide
  have hdescent : baseEnd_292969 < baseStart_292969 := by decide
  rcases family_descends (prefixWord ++ tailWord_292969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_292993 : List Nat := [1, 2, 4, 2, 3, 1, 1, 6]
def baseStart_292993 : Nat := 118140960795 + 292993 * 2 ^ 59
def prefixEnd_292993 : Nat := 4983230072969 + 3 ^ 40 * 292993 * 2
def baseEnd_292993 : Nat := 44576662934185895478535

theorem tailTrace_292993 : CollatzResearch.WordTrace tailWord_292993 prefixEnd_292993 44576662934185895478535 := by
  unfold tailWord_292993
  simp only [CollatzResearch.WordTrace]
  refine ⟨10686332627543875065683633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7124221751695916710455755 10686332627543875065683633)
  ·
    refine ⟨8014749470657906299262725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10686332627543875065683633 8014749470657906299262725)
    ·
      refine ⟨1502765525748357431111761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8014749470657906299262725 1502765525748357431111761)
      ·
        refine ⟨1127074144311268073333821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1502765525748357431111761 1127074144311268073333821)
        ·
          refine ⟨422652804116725527500183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1127074144311268073333821 422652804116725527500183)
          ·
            refine ⟨633979206175088291250275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422652804116725527500183 633979206175088291250275)
            ·
              refine ⟨950968809262632436875413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 633979206175088291250275 950968809262632436875413)
              ·
                refine ⟨44576662934185895478535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 950968809262632436875413 44576662934185895478535)
                ·
                  rfl

theorem cell20_292993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 6].length) (baseStart_292993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_292993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_292993 prefixEnd_292993 := by exact prefixLift 292993
  have htrace : WordTrace (prefixWord ++ tailWord_292993) baseStart_292993 baseEnd_292993 := by
    simpa [prefixWord, tailWord_292993, baseEnd_292993] using wordTrace_append hprefix tailTrace_292993
  have hstable : (prefixWord ++ tailWord_292993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_292993).length < 2 ^ (prefixWord ++ tailWord_292993).sum := by decide
  have hdescent : baseEnd_292993 < baseStart_292993 := by decide
  rcases family_descends (prefixWord ++ tailWord_292993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293000 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 5]
def baseStart_293000 : Nat := 118140960795 + 293000 * 2 ^ 59
def prefixEnd_293000 : Nat := 4983230072969 + 3 ^ 40 * 293000 * 2
def baseEnd_293000 : Nat := 133733183793296773202243

theorem tailTrace_293000 : CollatzResearch.WordTrace tailWord_293000 prefixEnd_293000 133733183793296773202243 := by
  unfold tailWord_293000
  simp only [CollatzResearch.WordTrace]
  refine ⟨5343293969259257630594227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7124391959012343507458969 5343293969259257630594227)
  ·
    refine ⟨8014940953888886445891341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5343293969259257630594227 8014940953888886445891341)
    ·
      refine ⟨3005602857708332417209253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8014940953888886445891341 3005602857708332417209253)
      ·
        refine ⟨563550535820312328226735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3005602857708332417209253 563550535820312328226735)
        ·
          refine ⟨845325803730468492340103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563550535820312328226735 845325803730468492340103)
          ·
            refine ⟨1267988705595702738510155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845325803730468492340103 1267988705595702738510155)
            ·
              refine ⟨1901983058393554107765233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1267988705595702738510155 1901983058393554107765233)
              ·
                refine ⟨1426487293795165580823925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1901983058393554107765233 1426487293795165580823925)
                ·
                  refine ⟨133733183793296773202243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1426487293795165580823925 133733183793296773202243)
                  ·
                    rfl

theorem cell20_293000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_293000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293000 prefixEnd_293000 := by exact prefixLift 293000
  have htrace : WordTrace (prefixWord ++ tailWord_293000) baseStart_293000 baseEnd_293000 := by
    simpa [prefixWord, tailWord_293000, baseEnd_293000] using wordTrace_append hprefix tailTrace_293000
  have hstable : (prefixWord ++ tailWord_293000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293000).length < 2 ^ (prefixWord ++ tailWord_293000).sum := by decide
  have hdescent : baseEnd_293000 < baseStart_293000 := by decide
  rcases family_descends (prefixWord ++ tailWord_293000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293024 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 4]
def baseStart_293024 : Nat := 118140960795 + 293024 * 2 ^ 59
def prefixEnd_293024 : Nat := 4983230072969 + 3 ^ 40 * 293024 * 2
def baseEnd_293024 : Nat := 133744138047259356402145

theorem tailTrace_293024 : CollatzResearch.WordTrace tailWord_293024 prefixEnd_293024 133744138047259356402145 := by
  unfold tailWord_293024
  simp only [CollatzResearch.WordTrace]
  refine ⟨5343731645215783680031063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7124975526954378240041417 5343731645215783680031063)
  ·
    refine ⟨8015597467823675520046595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5343731645215783680031063 8015597467823675520046595)
    ·
      refine ⟨12023396201735513280069893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8015597467823675520046595 12023396201735513280069893)
      ·
        refine ⟨2254386787825408740013105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12023396201735513280069893 2254386787825408740013105)
        ·
          refine ⟨1690790090869056555009829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2254386787825408740013105 1690790090869056555009829)
          ·
            refine ⟨317023142037948104064343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1690790090869056555009829 317023142037948104064343)
            ·
              refine ⟨475534713056922156096515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317023142037948104064343 475534713056922156096515)
              ·
                refine ⟨713302069585383234144773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 475534713056922156096515 713302069585383234144773)
                ·
                  refine ⟨133744138047259356402145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 713302069585383234144773 133744138047259356402145)
                  ·
                    rfl

theorem cell20_293024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_293024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293024 prefixEnd_293024 := by exact prefixLift 293024
  have htrace : WordTrace (prefixWord ++ tailWord_293024) baseStart_293024 baseEnd_293024 := by
    simpa [prefixWord, tailWord_293024, baseEnd_293024] using wordTrace_append hprefix tailTrace_293024
  have hstable : (prefixWord ++ tailWord_293024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293024).length < 2 ^ (prefixWord ++ tailWord_293024).sum := by decide
  have hdescent : baseEnd_293024 < baseStart_293024 := by decide
  rcases family_descends (prefixWord ++ tailWord_293024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293034 : List Nat := [3, 1, 5, 1, 2, 1, 1, 3, 3]
def baseStart_293034 : Nat := 118140960795 + 293034 * 2 ^ 59
def prefixEnd_293034 : Nat := 4983230072969 + 3 ^ 40 * 293034 * 2
def baseEnd_293034 : Nat := 133748702319743766068771

theorem tailTrace_293034 : CollatzResearch.WordTrace tailWord_293034 prefixEnd_293034 133748702319743766068771 := by
  unfold tailWord_293034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2671957005098834766981539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7125218680263559378617437 2671957005098834766981539)
  ·
    refine ⟨4007935507648252150472309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2671957005098834766981539 4007935507648252150472309)
    ·
      refine ⟨375743953842023639106779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4007935507648252150472309 375743953842023639106779)
      ·
        refine ⟨563615930763035458660169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375743953842023639106779 563615930763035458660169)
        ·
          refine ⟨422711948072276593995127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563615930763035458660169 422711948072276593995127)
          ·
            refine ⟨634067922108414890992691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422711948072276593995127 634067922108414890992691)
            ·
              refine ⟨951101883162622336489037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634067922108414890992691 951101883162622336489037)
              ·
                refine ⟨356663206185983376183389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 951101883162622336489037 356663206185983376183389)
                ·
                  refine ⟨133748702319743766068771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356663206185983376183389 133748702319743766068771)
                  ·
                    rfl

theorem cell20_293034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_293034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293034 prefixEnd_293034 := by exact prefixLift 293034
  have htrace : WordTrace (prefixWord ++ tailWord_293034) baseStart_293034 baseEnd_293034 := by
    simpa [prefixWord, tailWord_293034, baseEnd_293034] using wordTrace_append hprefix tailTrace_293034
  have hstable : (prefixWord ++ tailWord_293034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293034).length < 2 ^ (prefixWord ++ tailWord_293034).sum := by decide
  have hdescent : baseEnd_293034 < baseStart_293034 := by decide
  rcases family_descends (prefixWord ++ tailWord_293034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293127 : List Nat := [1, 1, 4, 5, 2, 1, 1, 2, 3]
def baseStart_293127 : Nat := 118140960795 + 293127 * 2 ^ 59
def prefixEnd_293127 : Nat := 4983230072969 + 3 ^ 40 * 293127 * 2
def baseEnd_293127 : Nat := 133791150053848775968391

theorem tailTrace_293127 : CollatzResearch.WordTrace tailWord_293127 prefixEnd_293127 133791150053848775968391 := by
  unfold tailWord_293127
  simp only [CollatzResearch.WordTrace]
  refine ⟨10691220009058415951061635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7127480006038943967374423 10691220009058415951061635)
  ·
    refine ⟨16036830013587623926592453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10691220009058415951061635 16036830013587623926592453)
    ·
      refine ⟨3006905627547679486236085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16036830013587623926592453 3006905627547679486236085)
      ·
        refine ⟨281897402582594951834633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3006905627547679486236085 281897402582594951834633)
        ·
          refine ⟨211423051936946213875975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281897402582594951834633 211423051936946213875975)
          ·
            refine ⟨317134577905419320813963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211423051936946213875975 317134577905419320813963)
            ·
              refine ⟨475701866858128981220945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317134577905419320813963 475701866858128981220945)
              ·
                refine ⟨356776400143596735915709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 475701866858128981220945 356776400143596735915709)
                ·
                  refine ⟨133791150053848775968391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 356776400143596735915709 133791150053848775968391)
                  ·
                    rfl

theorem cell20_293127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 3].length) (baseStart_293127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293127 prefixEnd_293127 := by exact prefixLift 293127
  have htrace : WordTrace (prefixWord ++ tailWord_293127) baseStart_293127 baseEnd_293127 := by
    simpa [prefixWord, tailWord_293127, baseEnd_293127] using wordTrace_append hprefix tailTrace_293127
  have hstable : (prefixWord ++ tailWord_293127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293127).length < 2 ^ (prefixWord ++ tailWord_293127).sum := by decide
  have hdescent : baseEnd_293127 < baseStart_293127 := by decide
  rcases family_descends (prefixWord ++ tailWord_293127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293128 : List Nat := [2, 1, 3, 2, 3, 2, 7]
def baseStart_293128 : Nat := 118140960795 + 293128 * 2 ^ 59
def prefixEnd_293128 : Nat := 4983230072969 + 3 ^ 40 * 293128 * 2
def baseEnd_293128 : Nat := 14865734053455246326117

theorem tailTrace_293128 : CollatzResearch.WordTrace tailWord_293128 prefixEnd_293128 14865734053455246326117 := by
  unfold tailWord_293128
  simp only [CollatzResearch.WordTrace]
  refine ⟨5345628241027396560924019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7127504321369862081232025 5345628241027396560924019)
  ·
    refine ⟨8018442361541094841386029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5345628241027396560924019 8018442361541094841386029)
    ·
      refine ⟨3006915885577910565519761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8018442361541094841386029 3006915885577910565519761)
      ·
        refine ⟨2255186914183432924139821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3006915885577910565519761 2255186914183432924139821)
        ·
          refine ⟨845695092818787346552433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2255186914183432924139821 845695092818787346552433)
          ·
            refine ⟨634271319614090509914325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 845695092818787346552433 634271319614090509914325)
            ·
              refine ⟨14865734053455246326117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 634271319614090509914325 14865734053455246326117)
              ·
                rfl

theorem cell20_293128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 7].length) (baseStart_293128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293128 prefixEnd_293128 := by exact prefixLift 293128
  have htrace : WordTrace (prefixWord ++ tailWord_293128) baseStart_293128 baseEnd_293128 := by
    simpa [prefixWord, tailWord_293128, baseEnd_293128] using wordTrace_append hprefix tailTrace_293128
  have hstable : (prefixWord ++ tailWord_293128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293128).length < 2 ^ (prefixWord ++ tailWord_293128).sum := by decide
  have hdescent : baseEnd_293128 < baseStart_293128 := by decide
  rcases family_descends (prefixWord ++ tailWord_293128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293172 : List Nat := [2, 5, 1, 1, 1, 4, 1, 3, 2]
def baseStart_293172 : Nat := 118140960795 + 293172 * 2 ^ 59
def prefixEnd_293172 : Nat := 4983230072969 + 3 ^ 40 * 293172 * 2
def baseEnd_293172 : Nat := 133811689280028619468207

theorem tailTrace_293172 : CollatzResearch.WordTrace tailWord_293172 prefixEnd_293172 133811689280028619468207 := by
  unfold tailWord_293172
  simp only [CollatzResearch.WordTrace]
  refine ⟨5346430646947694318224885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7128574195930259090966513 5346430646947694318224885)
  ·
    refine ⟨501227873151346342333583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5346430646947694318224885 501227873151346342333583)
    ·
      refine ⟨751841809727019513500375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 501227873151346342333583 751841809727019513500375)
      ·
        refine ⟨1127762714590529270250563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751841809727019513500375 1127762714590529270250563)
        ·
          refine ⟨1691644071885793905375845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1127762714590529270250563 1691644071885793905375845)
          ·
            refine ⟨317183263478586357257971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1691644071885793905375845 317183263478586357257971)
            ·
              refine ⟨475774895217879535886957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317183263478586357257971 475774895217879535886957)
              ·
                refine ⟨178415585706704825957609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 475774895217879535886957 178415585706704825957609)
                ·
                  refine ⟨133811689280028619468207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178415585706704825957609 133811689280028619468207)
                  ·
                    rfl

theorem cell20_293172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_293172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293172 prefixEnd_293172 := by exact prefixLift 293172
  have htrace : WordTrace (prefixWord ++ tailWord_293172) baseStart_293172 baseEnd_293172 := by
    simpa [prefixWord, tailWord_293172, baseEnd_293172] using wordTrace_append hprefix tailTrace_293172
  have hstable : (prefixWord ++ tailWord_293172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293172).length < 2 ^ (prefixWord ++ tailWord_293172).sum := by decide
  have hdescent : baseEnd_293172 < baseStart_293172 := by decide
  rcases family_descends (prefixWord ++ tailWord_293172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293173 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 7]
def baseStart_293173 : Nat := 118140960795 + 293173 * 2 ^ 59
def prefixEnd_293173 : Nat := 4983230072969 + 3 ^ 40 * 293173 * 2
def baseEnd_293173 : Nat := 133812145707277060434869

theorem tailTrace_293173 : CollatzResearch.WordTrace tailWord_293173 prefixEnd_293173 133812145707277060434869 := by
  unfold tailWord_293173
  simp only [CollatzResearch.WordTrace]
  refine ⟨10692897766891765807236173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7128598511261177204824115 10692897766891765807236173)
  ·
    refine ⟨4009836662584412177713565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10692897766891765807236173 4009836662584412177713565)
    ·
      refine ⟨1503688748469154566642587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4009836662584412177713565 1503688748469154566642587)
      ·
        refine ⟨2255533122703731849963881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1503688748469154566642587 2255533122703731849963881)
        ·
          refine ⟨1691649842027798887472911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2255533122703731849963881 1691649842027798887472911)
          ·
            refine ⟨2537474763041698331209367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1691649842027798887472911 2537474763041698331209367)
            ·
              refine ⟨3806212144562547496814051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2537474763041698331209367 3806212144562547496814051)
              ·
                refine ⟨5709318216843821245221077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3806212144562547496814051 5709318216843821245221077)
                ·
                  refine ⟨133812145707277060434869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5709318216843821245221077 133812145707277060434869)
                  ·
                    rfl

theorem cell20_293173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_293173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293173 prefixEnd_293173 := by exact prefixLift 293173
  have htrace : WordTrace (prefixWord ++ tailWord_293173) baseStart_293173 baseEnd_293173 := by
    simpa [prefixWord, tailWord_293173, baseEnd_293173] using wordTrace_append hprefix tailTrace_293173
  have hstable : (prefixWord ++ tailWord_293173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293173).length < 2 ^ (prefixWord ++ tailWord_293173).sum := by decide
  have hdescent : baseEnd_293173 < baseStart_293173 := by decide
  rcases family_descends (prefixWord ++ tailWord_293173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293176 : List Nat := [2, 1, 2, 1, 3, 1, 5, 3, 2]
def baseStart_293176 : Nat := 118140960795 + 293176 * 2 ^ 59
def prefixEnd_293176 : Nat := 4983230072969 + 3 ^ 40 * 293176 * 2
def baseEnd_293176 : Nat := 133813514989022383334857

theorem tailTrace_293176 : CollatzResearch.WordTrace tailWord_293176 prefixEnd_293176 133813514989022383334857 := by
  unfold tailWord_293176
  simp only [CollatzResearch.WordTrace]
  refine ⟨5346503592940448659797691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7128671457253931546396921 5346503592940448659797691)
  ·
    refine ⟨8019755389410672989696537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5346503592940448659797691 8019755389410672989696537)
    ·
      refine ⟨6014816542058004742272403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8019755389410672989696537 6014816542058004742272403)
      ·
        refine ⟨9022224813087007113408605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6014816542058004742272403 9022224813087007113408605)
        ·
          refine ⟨3383334304907627667528227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9022224813087007113408605 3383334304907627667528227)
          ·
            refine ⟨5075001457361441501292341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3383334304907627667528227 5075001457361441501292341)
            ·
              refine ⟨475781386627635140746157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5075001457361441501292341 475781386627635140746157)
              ·
                refine ⟨178418019985363177779809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 475781386627635140746157 178418019985363177779809)
                ·
                  refine ⟨133813514989022383334857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178418019985363177779809 133813514989022383334857)
                  ·
                    rfl

theorem cell20_293176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 2].length) (baseStart_293176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293176 prefixEnd_293176 := by exact prefixLift 293176
  have htrace : WordTrace (prefixWord ++ tailWord_293176) baseStart_293176 baseEnd_293176 := by
    simpa [prefixWord, tailWord_293176, baseEnd_293176] using wordTrace_append hprefix tailTrace_293176
  have hstable : (prefixWord ++ tailWord_293176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293176).length < 2 ^ (prefixWord ++ tailWord_293176).sum := by decide
  have hdescent : baseEnd_293176 < baseStart_293176 := by decide
  rcases family_descends (prefixWord ++ tailWord_293176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293187 : List Nat := [1, 1, 1, 3, 1, 3, 10]
def baseStart_293187 : Nat := 118140960795 + 293187 * 2 ^ 59
def prefixEnd_293187 : Nat := 4983230072969 + 3 ^ 40 * 293187 * 2
def baseEnd_293187 : Nat := 14868726187639470440905

theorem tailTrace_293187 : CollatzResearch.WordTrace tailWord_293187 prefixEnd_293187 14868726187639470440905 := by
  unfold tailWord_293187
  simp only [CollatzResearch.WordTrace]
  refine ⟨10693408388841046198245815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7128938925894030798830543 10693408388841046198245815)
  ·
    refine ⟨16040112583261569297368723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10693408388841046198245815 16040112583261569297368723)
    ·
      refine ⟨24060168874892353946053085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16040112583261569297368723 24060168874892353946053085)
      ·
        refine ⟨9022563328084632729769907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24060168874892353946053085 9022563328084632729769907)
        ·
          refine ⟨13533844992126949094654861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9022563328084632729769907 13533844992126949094654861)
          ·
            refine ⟨5075191872047605910495573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13533844992126949094654861 5075191872047605910495573)
            ·
              refine ⟨14868726187639470440905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5075191872047605910495573 14868726187639470440905)
              ·
                rfl

theorem cell20_293187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 10].length) (baseStart_293187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293187 prefixEnd_293187 := by exact prefixLift 293187
  have htrace : WordTrace (prefixWord ++ tailWord_293187) baseStart_293187 baseEnd_293187 := by
    simpa [prefixWord, tailWord_293187, baseEnd_293187] using wordTrace_append hprefix tailTrace_293187
  have hstable : (prefixWord ++ tailWord_293187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293187).length < 2 ^ (prefixWord ++ tailWord_293187).sum := by decide
  have hdescent : baseEnd_293187 < baseStart_293187 := by decide
  rcases family_descends (prefixWord ++ tailWord_293187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293204 : List Nat := [2, 4, 1, 1, 2, 2, 1, 7]
def baseStart_293204 : Nat := 118140960795 + 293204 * 2 ^ 59
def prefixEnd_293204 : Nat := 4983230072969 + 3 ^ 40 * 293204 * 2
def baseEnd_293204 : Nat := 44608764983992910133803

theorem tailTrace_293204 : CollatzResearch.WordTrace tailWord_293204 prefixEnd_293204 44608764983992910133803 := by
  unfold tailWord_293204
  simp only [CollatzResearch.WordTrace]
  refine ⟨5347014214889729050807333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7129352286519638734409777 5347014214889729050807333)
  ·
    refine ⟨1002565165291824197026375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5347014214889729050807333 1002565165291824197026375)
    ·
      refine ⟨1503847747937736295539563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1002565165291824197026375 1503847747937736295539563)
      ·
        refine ⟨2255771621906604443309345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1503847747937736295539563 2255771621906604443309345)
        ·
          refine ⟨1691828716429953332482009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2255771621906604443309345 1691828716429953332482009)
          ·
            refine ⟨1268871537322464999361507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1691828716429953332482009 1268871537322464999361507)
            ·
              refine ⟨1903307305983697499042261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268871537322464999361507 1903307305983697499042261)
              ·
                refine ⟨44608764983992910133803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1903307305983697499042261 44608764983992910133803)
                ·
                  rfl

theorem cell20_293204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_293204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293204 prefixEnd_293204 := by exact prefixLift 293204
  have htrace : WordTrace (prefixWord ++ tailWord_293204) baseStart_293204 baseEnd_293204 := by
    simpa [prefixWord, tailWord_293204, baseEnd_293204] using wordTrace_append hprefix tailTrace_293204
  have hstable : (prefixWord ++ tailWord_293204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293204).length < 2 ^ (prefixWord ++ tailWord_293204).sum := by decide
  have hdescent : baseEnd_293204 < baseStart_293204 := by decide
  rcases family_descends (prefixWord ++ tailWord_293204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293225 : List Nat := [1, 2, 1, 1, 1, 3, 3, 8]
def baseStart_293225 : Nat := 118140960795 + 293225 * 2 ^ 59
def prefixEnd_293225 : Nat := 4983230072969 + 3 ^ 40 * 293225 * 2
def baseEnd_293225 : Nat := 44611959974731996900441

theorem tailTrace_293225 : CollatzResearch.WordTrace tailWord_293225 prefixEnd_293225 44611959974731996900441 := by
  unfold tailWord_293225
  simp only [CollatzResearch.WordTrace]
  refine ⟨10694794362703378688129129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7129862908468919125419419 10694794362703378688129129)
  ·
    refine ⟨8021095772027534016096847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10694794362703378688129129 8021095772027534016096847)
    ·
      refine ⟨12031643658041301024145271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8021095772027534016096847 12031643658041301024145271)
      ·
        refine ⟨18047465487061951536217907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12031643658041301024145271 18047465487061951536217907)
        ·
          refine ⟨27071198230592927304326861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18047465487061951536217907 27071198230592927304326861)
          ·
            refine ⟨10151699336472347739122573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27071198230592927304326861 10151699336472347739122573)
            ·
              refine ⟨3806887251177130402170965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10151699336472347739122573 3806887251177130402170965)
              ·
                refine ⟨44611959974731996900441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3806887251177130402170965 44611959974731996900441)
                ·
                  rfl

theorem cell20_293225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 8].length) (baseStart_293225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293225 prefixEnd_293225 := by exact prefixLift 293225
  have htrace : WordTrace (prefixWord ++ tailWord_293225) baseStart_293225 baseEnd_293225 := by
    simpa [prefixWord, tailWord_293225, baseEnd_293225] using wordTrace_append hprefix tailTrace_293225
  have hstable : (prefixWord ++ tailWord_293225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293225).length < 2 ^ (prefixWord ++ tailWord_293225).sum := by decide
  have hdescent : baseEnd_293225 < baseStart_293225 := by decide
  rcases family_descends (prefixWord ++ tailWord_293225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293238 : List Nat := [5, 1, 1, 4, 2, 7]
def baseStart_293238 : Nat := 118140960795 + 293238 * 2 ^ 59
def prefixEnd_293238 : Nat := 4983230072969 + 3 ^ 40 * 293238 * 2
def baseEnd_293238 : Nat := 4957104202904656417331

theorem tailTrace_293238 : CollatzResearch.WordTrace tailWord_293238 prefixEnd_293238 4957104202904656417331 := by
  unfold tailWord_293238
  simp only [CollatzResearch.WordTrace]
  refine ⟨668454281978517619272023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7130179007770854605568245 668454281978517619272023)
  ·
    refine ⟨1002681422967776428908035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 668454281978517619272023 1002681422967776428908035)
    ·
      refine ⟨1504022134451664643362053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1002681422967776428908035 1504022134451664643362053)
      ·
        refine ⟨282004150209687120630385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1504022134451664643362053 282004150209687120630385)
        ·
          refine ⟨211503112657265340472789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282004150209687120630385 211503112657265340472789)
          ·
            refine ⟨4957104202904656417331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 211503112657265340472789 4957104202904656417331)
            ·
              rfl

theorem cell20_293238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 7].length) (baseStart_293238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293238 prefixEnd_293238 := by exact prefixLift 293238
  have htrace : WordTrace (prefixWord ++ tailWord_293238) baseStart_293238 baseEnd_293238 := by
    simpa [prefixWord, tailWord_293238, baseEnd_293238] using wordTrace_append hprefix tailTrace_293238
  have hstable : (prefixWord ++ tailWord_293238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293238).length < 2 ^ (prefixWord ++ tailWord_293238).sum := by decide
  have hdescent : baseEnd_293238 < baseStart_293238 := by decide
  rcases family_descends (prefixWord ++ tailWord_293238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293252 : List Nat := [2, 3, 2, 1, 1, 2, 3, 4, 2]
def baseStart_293252 : Nat := 118140960795 + 293252 * 2 ^ 59
def prefixEnd_293252 : Nat := 4983230072969 + 3 ^ 40 * 293252 * 2
def baseEnd_293252 : Nat := 133848203459903896801213

theorem tailTrace_293252 : CollatzResearch.WordTrace tailWord_293252 prefixEnd_293252 133848203459903896801213 := by
  unfold tailWord_293252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5347889566802781149681005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7130519422403708199574673 5347889566802781149681005)
  ·
    refine ⟨2005458587551042931130377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5347889566802781149681005 2005458587551042931130377)
    ·
      refine ⟨1504093940663282198347783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2005458587551042931130377 1504093940663282198347783)
      ·
        refine ⟨2256140910994923297521675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1504093940663282198347783 2256140910994923297521675)
        ·
          refine ⟨3384211366492384946282513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2256140910994923297521675 3384211366492384946282513)
          ·
            refine ⟨2538158524869288709711885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3384211366492384946282513 2538158524869288709711885)
            ·
              refine ⟨951809446825983266141957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2538158524869288709711885 951809446825983266141957)
              ·
                refine ⟨178464271279871862401617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 951809446825983266141957 178464271279871862401617)
                ·
                  refine ⟨133848203459903896801213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178464271279871862401617 133848203459903896801213)
                  ·
                    rfl

theorem cell20_293252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_293252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293252 prefixEnd_293252 := by exact prefixLift 293252
  have htrace : WordTrace (prefixWord ++ tailWord_293252) baseStart_293252 baseEnd_293252 := by
    simpa [prefixWord, tailWord_293252, baseEnd_293252] using wordTrace_append hprefix tailTrace_293252
  have hstable : (prefixWord ++ tailWord_293252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293252).length < 2 ^ (prefixWord ++ tailWord_293252).sum := by decide
  have hdescent : baseEnd_293252 < baseStart_293252 := by decide
  rcases family_descends (prefixWord ++ tailWord_293252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293300 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 5]
def baseStart_293300 : Nat := 118140960795 + 293300 * 2 ^ 59
def prefixEnd_293300 : Nat := 4983230072969 + 3 ^ 40 * 293300 * 2
def baseEnd_293300 : Nat := 133870111967829063201017

theorem tailTrace_293300 : CollatzResearch.WordTrace tailWord_293300 prefixEnd_293300 133870111967829063201017 := by
  unfold tailWord_293300
  simp only [CollatzResearch.WordTrace]
  refine ⟨5348764918715833248554677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7131686558287777664739569 5348764918715833248554677)
  ·
    refine ⟨501446711129609367052001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5348764918715833248554677 501446711129609367052001)
    ·
      refine ⟨376085033347207025289001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 501446711129609367052001 376085033347207025289001)
      ·
        refine ⟨282063775010405268966751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376085033347207025289001 282063775010405268966751)
        ·
          refine ⟨423095662515607903450127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282063775010405268966751 423095662515607903450127)
          ·
            refine ⟨634643493773411855175191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423095662515607903450127 634643493773411855175191)
            ·
              refine ⟨951965240660117782762787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634643493773411855175191 951965240660117782762787)
              ·
                refine ⟨1427947860990176674144181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 951965240660117782762787 1427947860990176674144181)
                ·
                  refine ⟨133870111967829063201017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1427947860990176674144181 133870111967829063201017)
                  ·
                    rfl

theorem cell20_293300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_293300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293300 prefixEnd_293300 := by exact prefixLift 293300
  have htrace : WordTrace (prefixWord ++ tailWord_293300) baseStart_293300 baseEnd_293300 := by
    simpa [prefixWord, tailWord_293300, baseEnd_293300] using wordTrace_append hprefix tailTrace_293300
  have hstable : (prefixWord ++ tailWord_293300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293300).length < 2 ^ (prefixWord ++ tailWord_293300).sum := by decide
  have hdescent : baseEnd_293300 < baseStart_293300 := by decide
  rcases family_descends (prefixWord ++ tailWord_293300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293362 : List Nat := [3, 2, 1, 4, 2, 1, 3, 2, 2]
def baseStart_293362 : Nat := 118140960795 + 293362 * 2 ^ 59
def prefixEnd_293362 : Nat := 4983230072969 + 3 ^ 40 * 293362 * 2
def baseEnd_293362 : Nat := 133898410457232403134097

theorem tailTrace_293362 : CollatzResearch.WordTrace tailWord_293362 prefixEnd_293362 133898410457232403134097 := by
  unfold tailWord_293362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2674947790801762771466585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7133194108804700723910893 2674947790801762771466585)
  ·
    refine ⟨2006210843101322078599939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2674947790801762771466585 2006210843101322078599939)
    ·
      refine ⟨3009316264651983117899909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2006210843101322078599939 3009316264651983117899909)
      ·
        refine ⟨564246799622246834606233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3009316264651983117899909 564246799622246834606233)
        ·
          refine ⟨423185099716685125954675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 564246799622246834606233 423185099716685125954675)
          ·
            refine ⟨634777649575027688932013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423185099716685125954675 634777649575027688932013)
            ·
              refine ⟨238041618590635383349505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 634777649575027688932013 238041618590635383349505)
              ·
                refine ⟨178531213942976537512129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238041618590635383349505 178531213942976537512129)
                ·
                  refine ⟨133898410457232403134097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178531213942976537512129 133898410457232403134097)
                  ·
                    rfl

theorem cell20_293362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_293362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293362 prefixEnd_293362 := by exact prefixLift 293362
  have htrace : WordTrace (prefixWord ++ tailWord_293362) baseStart_293362 baseEnd_293362 := by
    simpa [prefixWord, tailWord_293362, baseEnd_293362] using wordTrace_append hprefix tailTrace_293362
  have hstable : (prefixWord ++ tailWord_293362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293362).length < 2 ^ (prefixWord ++ tailWord_293362).sum := by decide
  have hdescent : baseEnd_293362 < baseStart_293362 := by decide
  rcases family_descends (prefixWord ++ tailWord_293362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293363 : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 3]
def baseStart_293363 : Nat := 118140960795 + 293363 * 2 ^ 59
def prefixEnd_293363 : Nat := 4983230072969 + 3 ^ 40 * 293363 * 2
def baseEnd_293363 : Nat := 133898866884480844100759

theorem tailTrace_293363 : CollatzResearch.WordTrace tailWord_293363 prefixEnd_293363 133898866884480844100759 := by
  unfold tailWord_293363
  simp only [CollatzResearch.WordTrace]
  refine ⟨10699827636203428256652743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7133218424135618837768495 10699827636203428256652743)
  ·
    refine ⟨16049741454305142384979115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10699827636203428256652743 16049741454305142384979115)
    ·
      refine ⟨24074612181457713577468673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16049741454305142384979115 24074612181457713577468673)
      ·
        refine ⟨18055959136093285183101505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24074612181457713577468673 18055959136093285183101505)
        ·
          refine ⟨13541969352069963887326129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18055959136093285183101505 13541969352069963887326129)
          ·
            refine ⟨10156477014052472915494597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13541969352069963887326129 10156477014052472915494597)
            ·
              refine ⟨1904339440134838671655237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10156477014052472915494597 1904339440134838671655237)
              ·
                refine ⟨357063645025282250935357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1904339440134838671655237 357063645025282250935357)
                ·
                  refine ⟨133898866884480844100759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357063645025282250935357 133898866884480844100759)
                  ·
                    rfl

theorem cell20_293363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 3].length) (baseStart_293363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293363 prefixEnd_293363 := by exact prefixLift 293363
  have htrace : WordTrace (prefixWord ++ tailWord_293363) baseStart_293363 baseEnd_293363 := by
    simpa [prefixWord, tailWord_293363, baseEnd_293363] using wordTrace_append hprefix tailTrace_293363
  have hstable : (prefixWord ++ tailWord_293363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293363).length < 2 ^ (prefixWord ++ tailWord_293363).sum := by decide
  have hdescent : baseEnd_293363 < baseStart_293363 := by decide
  rcases family_descends (prefixWord ++ tailWord_293363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293370 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 4]
def baseStart_293370 : Nat := 118140960795 + 293370 * 2 ^ 59
def prefixEnd_293370 : Nat := 4983230072969 + 3 ^ 40 * 293370 * 2
def baseEnd_293370 : Nat := 133902061875219930867397

theorem tailTrace_293370 : CollatzResearch.WordTrace tailWord_293370 prefixEnd_293370 133902061875219930867397 := by
  unfold tailWord_293370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2675020736794517113039391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7133388631452045634771709 2675020736794517113039391)
  ·
    refine ⟨4012531105191775669559087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2675020736794517113039391 4012531105191775669559087)
    ·
      refine ⟨6018796657787663504338631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4012531105191775669559087 6018796657787663504338631)
      ·
        refine ⟨9028194986681495256507947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6018796657787663504338631 9028194986681495256507947)
        ·
          refine ⟨13542292480022242884761921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9028194986681495256507947 13542292480022242884761921)
          ·
            refine ⟨10156719360016682163571441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13542292480022242884761921 10156719360016682163571441)
            ·
              refine ⟨7617539520012511622678581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10156719360016682163571441 7617539520012511622678581)
              ·
                refine ⟨714144330001172964626117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7617539520012511622678581 714144330001172964626117)
                ·
                  refine ⟨133902061875219930867397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 714144330001172964626117 133902061875219930867397)
                  ·
                    rfl

theorem cell20_293370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_293370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293370 prefixEnd_293370 := by exact prefixLift 293370
  have htrace : WordTrace (prefixWord ++ tailWord_293370) baseStart_293370 baseEnd_293370 := by
    simpa [prefixWord, tailWord_293370, baseEnd_293370] using wordTrace_append hprefix tailTrace_293370
  have hstable : (prefixWord ++ tailWord_293370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293370).length < 2 ^ (prefixWord ++ tailWord_293370).sum := by decide
  have hdescent : baseEnd_293370 < baseStart_293370 := by decide
  rcases family_descends (prefixWord ++ tailWord_293370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293418 : List Nat := [3, 1, 4, 1, 1, 2, 1, 4, 3]
def baseStart_293418 : Nat := 118140960795 + 293418 * 2 ^ 59
def prefixEnd_293418 : Nat := 4983230072969 + 3 ^ 40 * 293418 * 2
def baseEnd_293418 : Nat := 133923970383145097267201

theorem tailTrace_293418 : CollatzResearch.WordTrace tailWord_293418 prefixEnd_293418 133923970383145097267201 := by
  unfold tailWord_293418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2675458412751043162476227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7134555767336115099936605 2675458412751043162476227)
  ·
    refine ⟨4013187619126564743714341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2675458412751043162476227 4013187619126564743714341)
    ·
      refine ⟨752472678586230889446439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4013187619126564743714341 752472678586230889446439)
      ·
        refine ⟨1128709017879346334169659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 752472678586230889446439 1128709017879346334169659)
        ·
          refine ⟨1693063526819019501254489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1128709017879346334169659 1693063526819019501254489)
          ·
            refine ⟨1269797645114264625940867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1693063526819019501254489 1269797645114264625940867)
            ·
              refine ⟨1904696467671396938911301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1269797645114264625940867 1904696467671396938911301)
              ·
                refine ⟨357130587688386926045869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1904696467671396938911301 357130587688386926045869)
                ·
                  refine ⟨133923970383145097267201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357130587688386926045869 133923970383145097267201)
                  ·
                    rfl

theorem cell20_293418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_293418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293418 prefixEnd_293418 := by exact prefixLift 293418
  have htrace : WordTrace (prefixWord ++ tailWord_293418) baseStart_293418 baseEnd_293418 := by
    simpa [prefixWord, tailWord_293418, baseEnd_293418] using wordTrace_append hprefix tailTrace_293418
  have hstable : (prefixWord ++ tailWord_293418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293418).length < 2 ^ (prefixWord ++ tailWord_293418).sum := by decide
  have hdescent : baseEnd_293418 < baseStart_293418 := by decide
  rcases family_descends (prefixWord ++ tailWord_293418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293439 : List Nat := [1, 1, 2, 2, 3, 2, 1, 5, 3]
def baseStart_293439 : Nat := 118140960795 + 293439 * 2 ^ 59
def prefixEnd_293439 : Nat := 4983230072969 + 3 ^ 40 * 293439 * 2
def baseEnd_293439 : Nat := 133933555355362357567115

theorem tailTrace_293439 : CollatzResearch.WordTrace tailWord_293439 prefixEnd_293439 133933555355362357567115 := by
  unfold tailWord_293439
  simp only [CollatzResearch.WordTrace]
  refine ⟨10702599583928093236419371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7135066389285395490946247 10702599583928093236419371)
  ·
    refine ⟨16053899375892139854629057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10702599583928093236419371 16053899375892139854629057)
    ·
      refine ⟨12040424531919104890971793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16053899375892139854629057 12040424531919104890971793)
      ·
        refine ⟨9030318398939328668228845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12040424531919104890971793 9030318398939328668228845)
        ·
          refine ⟨3386369399602248250585817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9030318398939328668228845 3386369399602248250585817)
          ·
            refine ⟨2539777049701686187939363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3386369399602248250585817 2539777049701686187939363)
            ·
              refine ⟨3809665574552529281909045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2539777049701686187939363 3809665574552529281909045)
              ·
                refine ⟨357156147614299620178973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3809665574552529281909045 357156147614299620178973)
                ·
                  refine ⟨133933555355362357567115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357156147614299620178973 133933555355362357567115)
                  ·
                    rfl

theorem cell20_293439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 3].length) (baseStart_293439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293439 prefixEnd_293439 := by exact prefixLift 293439
  have htrace : WordTrace (prefixWord ++ tailWord_293439) baseStart_293439 baseEnd_293439 := by
    simpa [prefixWord, tailWord_293439, baseEnd_293439] using wordTrace_append hprefix tailTrace_293439
  have hstable : (prefixWord ++ tailWord_293439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293439).length < 2 ^ (prefixWord ++ tailWord_293439).sum := by decide
  have hdescent : baseEnd_293439 < baseStart_293439 := by decide
  rcases family_descends (prefixWord ++ tailWord_293439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293480 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 4]
def baseStart_293480 : Nat := 118140960795 + 293480 * 2 ^ 59
def prefixEnd_293480 : Nat := 4983230072969 + 3 ^ 40 * 293480 * 2
def baseEnd_293480 : Nat := 133952268872548437200281

theorem tailTrace_293480 : CollatzResearch.WordTrace tailWord_293480 prefixEnd_293480 133952268872548437200281 := by
  unfold tailWord_293480
  simp only [CollatzResearch.WordTrace]
  refine ⟨5352047488389778619330947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7136063317853038159107929 5352047488389778619330947)
  ·
    refine ⟨8028071232584667928996421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5352047488389778619330947 8028071232584667928996421)
    ·
      refine ⟨1505263356109625236686829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8028071232584667928996421 1505263356109625236686829)
      ·
        refine ⟨564473758541109463757561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1505263356109625236686829 564473758541109463757561)
        ·
          refine ⟨423355318905832097818171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 564473758541109463757561 423355318905832097818171)
          ·
            refine ⟨635032978358748146727257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423355318905832097818171 635032978358748146727257)
            ·
              refine ⟨476274733769061110045443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 635032978358748146727257 476274733769061110045443)
              ·
                refine ⟨714412100653591665068165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476274733769061110045443 714412100653591665068165)
                ·
                  refine ⟨133952268872548437200281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 714412100653591665068165 133952268872548437200281)
                  ·
                    rfl

theorem cell20_293480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_293480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293480 prefixEnd_293480 := by exact prefixLift 293480
  have htrace : WordTrace (prefixWord ++ tailWord_293480) baseStart_293480 baseEnd_293480 := by
    simpa [prefixWord, tailWord_293480, baseEnd_293480] using wordTrace_append hprefix tailTrace_293480
  have hstable : (prefixWord ++ tailWord_293480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293480).length < 2 ^ (prefixWord ++ tailWord_293480).sum := by decide
  have hdescent : baseEnd_293480 < baseStart_293480 := by decide
  rcases family_descends (prefixWord ++ tailWord_293480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293484 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 4]
def baseStart_293484 : Nat := 118140960795 + 293484 * 2 ^ 59
def prefixEnd_293484 : Nat := 4983230072969 + 3 ^ 40 * 293484 * 2
def baseEnd_293484 : Nat := 133954094581542201066931

theorem tailTrace_293484 : CollatzResearch.WordTrace tailWord_293484 prefixEnd_293484 133954094581542201066931 := by
  unfold tailWord_293484
  simp only [CollatzResearch.WordTrace]
  refine ⟨5352120434382532960903753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7136160579176710614538337 5352120434382532960903753)
  ·
    refine ⟨4014090325786899720677815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5352120434382532960903753 4014090325786899720677815)
    ·
      refine ⟨6021135488680349581016723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4014090325786899720677815 6021135488680349581016723)
      ·
        refine ⟨9031703233020524371525085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6021135488680349581016723 9031703233020524371525085)
        ·
          refine ⟨3386888712382696639321907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9031703233020524371525085 3386888712382696639321907)
          ·
            refine ⟨5080333068574044958982861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3386888712382696639321907 5080333068574044958982861)
            ·
              refine ⟨1905124900715266859618573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5080333068574044958982861 1905124900715266859618573)
              ·
                refine ⟨714421837768225072356965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1905124900715266859618573 714421837768225072356965)
                ·
                  refine ⟨133954094581542201066931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 714421837768225072356965 133954094581542201066931)
                  ·
                    rfl

theorem cell20_293484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_293484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293484 prefixEnd_293484 := by exact prefixLift 293484
  have htrace : WordTrace (prefixWord ++ tailWord_293484) baseStart_293484 baseEnd_293484 := by
    simpa [prefixWord, tailWord_293484, baseEnd_293484] using wordTrace_append hprefix tailTrace_293484
  have hstable : (prefixWord ++ tailWord_293484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293484).length < 2 ^ (prefixWord ++ tailWord_293484).sum := by decide
  have hdescent : baseEnd_293484 < baseStart_293484 := by decide
  rcases family_descends (prefixWord ++ tailWord_293484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293508 : List Nat := [2, 3, 2, 1, 3, 2, 1, 6]
def baseStart_293508 : Nat := 118140960795 + 293508 * 2 ^ 59
def prefixEnd_293508 : Nat := 4983230072969 + 3 ^ 40 * 293508 * 2
def baseEnd_293508 : Nat := 44655016278501594755611

theorem tailTrace_293508 : CollatzResearch.WordTrace tailWord_293508 prefixEnd_293508 44655016278501594755611 := by
  unfold tailWord_293508
  simp only [CollatzResearch.WordTrace]
  refine ⟨5352558110339059010340589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7136744147118745347120785 5352558110339059010340589)
  ·
    refine ⟨2007209291377147128877721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5352558110339059010340589 2007209291377147128877721)
    ·
      refine ⟨1505406968532860346658291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2007209291377147128877721 1505406968532860346658291)
      ·
        refine ⟨2258110452799290519987437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1505406968532860346658291 2258110452799290519987437)
        ·
          refine ⟨846791419799733944995289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2258110452799290519987437 846791419799733944995289)
          ·
            refine ⟨635093564849800458746467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 846791419799733944995289 635093564849800458746467)
            ·
              refine ⟨952640347274700688119701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 635093564849800458746467 952640347274700688119701)
              ·
                refine ⟨44655016278501594755611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 952640347274700688119701 44655016278501594755611)
                ·
                  rfl

theorem cell20_293508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_293508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293508 prefixEnd_293508 := by exact prefixLift 293508
  have htrace : WordTrace (prefixWord ++ tailWord_293508) baseStart_293508 baseEnd_293508 := by
    simpa [prefixWord, tailWord_293508, baseEnd_293508] using wordTrace_append hprefix tailTrace_293508
  have hstable : (prefixWord ++ tailWord_293508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293508).length < 2 ^ (prefixWord ++ tailWord_293508).sum := by decide
  have hdescent : baseEnd_293508 < baseStart_293508 := by decide
  rcases family_descends (prefixWord ++ tailWord_293508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293514 : List Nat := [3, 1, 2, 3, 4, 1, 1, 3, 2]
def baseStart_293514 : Nat := 118140960795 + 293514 * 2 ^ 59
def prefixEnd_293514 : Nat := 4983230072969 + 3 ^ 40 * 293514 * 2
def baseEnd_293514 : Nat := 133967787398995430066809

theorem tailTrace_293514 : CollatzResearch.WordTrace tailWord_293514 prefixEnd_293514 133967787398995430066809 := by
  unfold tailWord_293514
  simp only [CollatzResearch.WordTrace]
  refine ⟨2676333764664095261349899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7136890039104254030266397 2676333764664095261349899)
  ·
    refine ⟨4014500646996142892024849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2676333764664095261349899 4014500646996142892024849)
    ·
      refine ⟨3010875485247107169018637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4014500646996142892024849 3010875485247107169018637)
      ·
        refine ⟨1129078306967665188381989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3010875485247107169018637 1129078306967665188381989)
        ·
          refine ⟨211702182556437222821623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1129078306967665188381989 211702182556437222821623)
          ·
            refine ⟨317553273834655834232435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211702182556437222821623 317553273834655834232435)
            ·
              refine ⟨476329910751983751348653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317553273834655834232435 476329910751983751348653)
              ·
                refine ⟨178623716531993906755745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 476329910751983751348653 178623716531993906755745)
                ·
                  refine ⟨133967787398995430066809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178623716531993906755745 133967787398995430066809)
                  ·
                    rfl

theorem cell20_293514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_293514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293514 prefixEnd_293514 := by exact prefixLift 293514
  have htrace : WordTrace (prefixWord ++ tailWord_293514) baseStart_293514 baseEnd_293514 := by
    simpa [prefixWord, tailWord_293514, baseEnd_293514] using wordTrace_append hprefix tailTrace_293514
  have hstable : (prefixWord ++ tailWord_293514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293514).length < 2 ^ (prefixWord ++ tailWord_293514).sum := by decide
  have hdescent : baseEnd_293514 < baseStart_293514 := by decide
  rcases family_descends (prefixWord ++ tailWord_293514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293549 : List Nat := [1, 5, 2, 1, 1, 2, 4, 1, 3]
def baseStart_293549 : Nat := 118140960795 + 293549 * 2 ^ 59
def prefixEnd_293549 : Nat := 4983230072969 + 3 ^ 40 * 293549 * 2
def baseEnd_293549 : Nat := 133983762352690863899999

theorem tailTrace_293549 : CollatzResearch.WordTrace tailWord_293549 prefixEnd_293549 133983762352690863899999 := by
  unfold tailWord_293549
  simp only [CollatzResearch.WordTrace]
  refine ⟨10706611613529582022923701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7137741075686388015282467 10706611613529582022923701)
  ·
    refine ⟨1003744838768398314649097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10706611613529582022923701 1003744838768398314649097)
    ·
      refine ⟨752808629076298735986823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1003744838768398314649097 752808629076298735986823)
      ·
        refine ⟨1129212943614448103980235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 752808629076298735986823 1129212943614448103980235)
        ·
          refine ⟨1693819415421672155970353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1129212943614448103980235 1693819415421672155970353)
          ·
            refine ⟨1270364561566254116977765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1693819415421672155970353 1270364561566254116977765)
            ·
              refine ⟨238193355293672646933331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1270364561566254116977765 238193355293672646933331)
              ·
                refine ⟨357290032940508970399997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238193355293672646933331 357290032940508970399997)
                ·
                  refine ⟨133983762352690863899999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357290032940508970399997 133983762352690863899999)
                  ·
                    rfl

theorem cell20_293549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_293549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293549 prefixEnd_293549 := by exact prefixLift 293549
  have htrace : WordTrace (prefixWord ++ tailWord_293549) baseStart_293549 baseEnd_293549 := by
    simpa [prefixWord, tailWord_293549, baseEnd_293549] using wordTrace_append hprefix tailTrace_293549
  have hstable : (prefixWord ++ tailWord_293549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293549).length < 2 ^ (prefixWord ++ tailWord_293549).sum := by decide
  have hdescent : baseEnd_293549 < baseStart_293549 := by decide
  rcases family_descends (prefixWord ++ tailWord_293549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293567 : List Nat := [1, 1, 2, 2, 2, 4, 2, 6]
def baseStart_293567 : Nat := 118140960795 + 293567 * 2 ^ 59
def prefixEnd_293567 : Nat := 4983230072969 + 3 ^ 40 * 293567 * 2
def baseEnd_293567 : Nat := 44663992681054267099975

theorem tailTrace_293567 : CollatzResearch.WordTrace tailWord_293567 prefixEnd_293567 44663992681054267099975 := by
  unfold tailWord_293567
  simp only [CollatzResearch.WordTrace]
  refine ⟨10707268127464371097078955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7138178751642914064719303 10707268127464371097078955)
  ·
    refine ⟨16060902191196556645618433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10707268127464371097078955 16060902191196556645618433)
    ·
      refine ⟨12045676643397417484213825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16060902191196556645618433 12045676643397417484213825)
      ·
        refine ⟨9034257482548063113160369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12045676643397417484213825 9034257482548063113160369)
        ·
          refine ⟨6775693111911047334870277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9034257482548063113160369 6775693111911047334870277)
          ·
            refine ⟨1270442458483321375288177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6775693111911047334870277 1270442458483321375288177)
            ·
              refine ⟨952831843862491031466133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1270442458483321375288177 952831843862491031466133)
              ·
                refine ⟨44663992681054267099975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 952831843862491031466133 44663992681054267099975)
                ·
                  rfl

theorem cell20_293567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 6].length) (baseStart_293567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293567 prefixEnd_293567 := by exact prefixLift 293567
  have htrace : WordTrace (prefixWord ++ tailWord_293567) baseStart_293567 baseEnd_293567 := by
    simpa [prefixWord, tailWord_293567, baseEnd_293567] using wordTrace_append hprefix tailTrace_293567
  have hstable : (prefixWord ++ tailWord_293567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293567).length < 2 ^ (prefixWord ++ tailWord_293567).sum := by decide
  have hdescent : baseEnd_293567 < baseStart_293567 := by decide
  rcases family_descends (prefixWord ++ tailWord_293567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293591 : List Nat := [1, 1, 3, 2, 1, 4, 1, 4, 3]
def baseStart_293591 : Nat := 118140960795 + 293591 * 2 ^ 59
def prefixEnd_293591 : Nat := 4983230072969 + 3 ^ 40 * 293591 * 2
def baseEnd_293591 : Nat := 134002932297125384499827

theorem tailTrace_293591 : CollatzResearch.WordTrace tailWord_293591 prefixEnd_293591 134002932297125384499827 := by
  unfold tailWord_293591
  simp only [CollatzResearch.WordTrace]
  refine ⟨10708143479377423195952627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7138762319584948797301751 10708143479377423195952627)
  ·
    refine ⟨16062215219066134793928941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10708143479377423195952627 16062215219066134793928941)
    ·
      refine ⟨6023330707149800547723353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16062215219066134793928941 6023330707149800547723353)
      ·
        refine ⟨4517498030362350410792515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6023330707149800547723353 4517498030362350410792515)
        ·
          refine ⟨6776247045543525616188773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4517498030362350410792515 6776247045543525616188773)
          ·
            refine ⟨1270546321039411053035395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6776247045543525616188773 1270546321039411053035395)
            ·
              refine ⟨1905819481559116579553093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1270546321039411053035395 1905819481559116579553093)
              ·
                refine ⟨357341152792334358666205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1905819481559116579553093 357341152792334358666205)
                ·
                  refine ⟨134002932297125384499827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357341152792334358666205 134002932297125384499827)
                  ·
                    rfl

theorem cell20_293591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 3].length) (baseStart_293591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293591 prefixEnd_293591 := by exact prefixLift 293591
  have htrace : WordTrace (prefixWord ++ tailWord_293591) baseStart_293591 baseEnd_293591 := by
    simpa [prefixWord, tailWord_293591, baseEnd_293591] using wordTrace_append hprefix tailTrace_293591
  have hstable : (prefixWord ++ tailWord_293591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293591).length < 2 ^ (prefixWord ++ tailWord_293591).sum := by decide
  have hdescent : baseEnd_293591 < baseStart_293591 := by decide
  rcases family_descends (prefixWord ++ tailWord_293591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293612 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_293612 : Nat := 118140960795 + 293612 * 2 ^ 59
def prefixEnd_293612 : Nat := 4983230072969 + 3 ^ 40 * 293612 * 2
def baseEnd_293612 : Nat := 134012517269342644799741

theorem tailTrace_293612 : CollatzResearch.WordTrace tailWord_293612 prefixEnd_293612 134012517269342644799741 := by
  unfold tailWord_293612
  simp only [CollatzResearch.WordTrace]
  refine ⟨5354454706150671891233545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7139272941534229188311393 5354454706150671891233545)
  ·
    refine ⟨4015841029613003918425159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5354454706150671891233545 4015841029613003918425159)
    ·
      refine ⟨6023761544419505877637739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4015841029613003918425159 6023761544419505877637739)
      ·
        refine ⟨9035642316629258816456609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6023761544419505877637739 9035642316629258816456609)
        ·
          refine ⟨6776731737471944112342457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9035642316629258816456609 6776731737471944112342457)
          ·
            refine ⟨5082548803103958084256843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6776731737471944112342457 5082548803103958084256843)
            ·
              refine ⟨7623823204655937126385265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5082548803103958084256843 7623823204655937126385265)
              ·
                refine ⟨5717867403491952844788949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7623823204655937126385265 5717867403491952844788949)
                ·
                  refine ⟨134012517269342644799741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5717867403491952844788949 134012517269342644799741)
                  ·
                    rfl

theorem cell20_293612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_293612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293612 prefixEnd_293612 := by exact prefixLift 293612
  have htrace : WordTrace (prefixWord ++ tailWord_293612) baseStart_293612 baseEnd_293612 := by
    simpa [prefixWord, tailWord_293612, baseEnd_293612] using wordTrace_append hprefix tailTrace_293612
  have hstable : (prefixWord ++ tailWord_293612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293612).length < 2 ^ (prefixWord ++ tailWord_293612).sum := by decide
  have hdescent : baseEnd_293612 < baseStart_293612 := by decide
  rcases family_descends (prefixWord ++ tailWord_293612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293636 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 6]
def baseStart_293636 : Nat := 118140960795 + 293636 * 2 ^ 59
def prefixEnd_293636 : Nat := 4983230072969 + 3 ^ 40 * 293636 * 2
def baseEnd_293636 : Nat := 134023471523305227999643

theorem tailTrace_293636 : CollatzResearch.WordTrace tailWord_293636 prefixEnd_293636 134023471523305227999643 := by
  unfold tailWord_293636
  simp only [CollatzResearch.WordTrace]
  refine ⟨5354892382107197940670381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7139856509476263920893841 5354892382107197940670381)
  ·
    refine ⟨2008084643290199227751393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5354892382107197940670381 2008084643290199227751393)
    ·
      refine ⟨1506063482467649420813545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2008084643290199227751393 1506063482467649420813545)
      ·
        refine ⟨1129547611850737065610159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1506063482467649420813545 1129547611850737065610159)
        ·
          refine ⟨1694321417776105598415239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1129547611850737065610159 1694321417776105598415239)
          ·
            refine ⟨2541482126664158397622859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1694321417776105598415239 2541482126664158397622859)
            ·
              refine ⟨3812223189996237596434289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2541482126664158397622859 3812223189996237596434289)
              ·
                refine ⟨2859167392497178197325717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3812223189996237596434289 2859167392497178197325717)
                ·
                  refine ⟨134023471523305227999643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2859167392497178197325717 134023471523305227999643)
                  ·
                    rfl

theorem cell20_293636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_293636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293636 prefixEnd_293636 := by exact prefixLift 293636
  have htrace : WordTrace (prefixWord ++ tailWord_293636) baseStart_293636 baseEnd_293636 := by
    simpa [prefixWord, tailWord_293636, baseEnd_293636] using wordTrace_append hprefix tailTrace_293636
  have hstable : (prefixWord ++ tailWord_293636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293636).length < 2 ^ (prefixWord ++ tailWord_293636).sum := by decide
  have hdescent : baseEnd_293636 < baseStart_293636 := by decide
  rcases family_descends (prefixWord ++ tailWord_293636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293653 : List Nat := [1, 3, 2, 1, 2, 2, 1, 6, 2]
def baseStart_293653 : Nat := 118140960795 + 293653 * 2 ^ 59
def prefixEnd_293653 : Nat := 4983230072969 + 3 ^ 40 * 293653 * 2
def baseEnd_293653 : Nat := 134031230786528724432907

theorem tailTrace_293653 : CollatzResearch.WordTrace tailWord_293653 prefixEnd_293653 134031230786528724432907 := by
  unfold tailWord_293653
  simp only [CollatzResearch.WordTrace]
  refine ⟨10710404805152807784709613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7140269870101871856473075 10710404805152807784709613)
  ·
    refine ⟨4016401801932302919266105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10710404805152807784709613 4016401801932302919266105)
    ·
      refine ⟨3012301351449227189449579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4016401801932302919266105 3012301351449227189449579)
      ·
        refine ⟨4518452027173840784174369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3012301351449227189449579 4518452027173840784174369)
        ·
          refine ⟨3388839020380380588130777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4518452027173840784174369 3388839020380380588130777)
          ·
            refine ⟨2541629265285285441098083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3388839020380380588130777 2541629265285285441098083)
            ·
              refine ⟨3812443897927928161647125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2541629265285285441098083 3812443897927928161647125)
              ·
                refine ⟨178708307715371632577209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3812443897927928161647125 178708307715371632577209)
                ·
                  refine ⟨134031230786528724432907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 178708307715371632577209 134031230786528724432907)
                  ·
                    rfl

theorem cell20_293653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_293653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293653 prefixEnd_293653 := by exact prefixLift 293653
  have htrace : WordTrace (prefixWord ++ tailWord_293653) baseStart_293653 baseEnd_293653 := by
    simpa [prefixWord, tailWord_293653, baseEnd_293653] using wordTrace_append hprefix tailTrace_293653
  have hstable : (prefixWord ++ tailWord_293653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293653).length < 2 ^ (prefixWord ++ tailWord_293653).sum := by decide
  have hdescent : baseEnd_293653 < baseStart_293653 := by decide
  rcases family_descends (prefixWord ++ tailWord_293653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293681 : List Nat := [1, 2, 2, 3, 2, 1, 3, 6]
def baseStart_293681 : Nat := 118140960795 + 293681 * 2 ^ 59
def prefixEnd_293681 : Nat := 4983230072969 + 3 ^ 40 * 293681 * 2
def baseEnd_293681 : Nat := 44681336916495023833153

theorem tailTrace_293681 : CollatzResearch.WordTrace tailWord_293681 prefixEnd_293681 44681336916495023833153 := by
  unfold tailWord_293681
  simp only [CollatzResearch.WordTrace]
  refine ⟨10711426049051368566728897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7140950699367579044485931 10711426049051368566728897)
  ·
    refine ⟨8033569536788526425046673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10711426049051368566728897 8033569536788526425046673)
    ·
      refine ⟨6025177152591394818785005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8033569536788526425046673 6025177152591394818785005)
      ·
        refine ⟨2259441432221773057044377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6025177152591394818785005 2259441432221773057044377)
        ·
          refine ⟨1694581074166329792783283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2259441432221773057044377 1694581074166329792783283)
          ·
            refine ⟨2541871611249494689174925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1694581074166329792783283 2541871611249494689174925)
            ·
              refine ⟨953201854218560508440597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2541871611249494689174925 953201854218560508440597)
              ·
                refine ⟨44681336916495023833153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 953201854218560508440597 44681336916495023833153)
                ·
                  rfl

theorem cell20_293681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 6].length) (baseStart_293681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293681 prefixEnd_293681 := by exact prefixLift 293681
  have htrace : WordTrace (prefixWord ++ tailWord_293681) baseStart_293681 baseEnd_293681 := by
    simpa [prefixWord, tailWord_293681, baseEnd_293681] using wordTrace_append hprefix tailTrace_293681
  have hstable : (prefixWord ++ tailWord_293681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293681).length < 2 ^ (prefixWord ++ tailWord_293681).sum := by decide
  have hdescent : baseEnd_293681 < baseStart_293681 := by decide
  rcases family_descends (prefixWord ++ tailWord_293681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293688 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 7]
def baseStart_293688 : Nat := 118140960795 + 293688 * 2 ^ 59
def prefixEnd_293688 : Nat := 4983230072969 + 3 ^ 40 * 293688 * 2
def baseEnd_293688 : Nat := 134047205740224158266097

theorem tailTrace_293688 : CollatzResearch.WordTrace tailWord_293688 prefixEnd_293688 134047205740224158266097 := by
  unfold tailWord_293688
  simp only [CollatzResearch.WordTrace]
  refine ⟨5355840680013004381116859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7141120906684005841489145 5355840680013004381116859)
  ·
    refine ⟨8033761020019506571675289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5355840680013004381116859 8033761020019506571675289)
    ·
      refine ⟨6025320765014629928756467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8033761020019506571675289 6025320765014629928756467)
      ·
        refine ⟨9037981147521944893134701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6025320765014629928756467 9037981147521944893134701)
        ·
          refine ⟨3389242930320729334925513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9037981147521944893134701 3389242930320729334925513)
          ·
            refine ⟨2541932197740547001194135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3389242930320729334925513 2541932197740547001194135)
            ·
              refine ⟨3812898296610820501791203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2541932197740547001194135 3812898296610820501791203)
              ·
                refine ⟨5719347444916230752686805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3812898296610820501791203 5719347444916230752686805)
                ·
                  refine ⟨134047205740224158266097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5719347444916230752686805 134047205740224158266097)
                  ·
                    rfl

theorem cell20_293688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_293688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293688 prefixEnd_293688 := by exact prefixLift 293688
  have htrace : WordTrace (prefixWord ++ tailWord_293688) baseStart_293688 baseEnd_293688 := by
    simpa [prefixWord, tailWord_293688, baseEnd_293688] using wordTrace_append hprefix tailTrace_293688
  have hstable : (prefixWord ++ tailWord_293688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293688).length < 2 ^ (prefixWord ++ tailWord_293688).sum := by decide
  have hdescent : baseEnd_293688 < baseStart_293688 := by decide
  rcases family_descends (prefixWord ++ tailWord_293688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293712 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 4]
def baseStart_293712 : Nat := 118140960795 + 293712 * 2 ^ 59
def prefixEnd_293712 : Nat := 4983230072969 + 3 ^ 40 * 293712 * 2
def baseEnd_293712 : Nat := 134058159994186741465999

theorem tailTrace_293712 : CollatzResearch.WordTrace tailWord_293712 prefixEnd_293712 134058159994186741465999 := by
  unfold tailWord_293712
  simp only [CollatzResearch.WordTrace]
  refine ⟨5356278355969530430553695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7141704474626040574071593 5356278355969530430553695)
  ·
    refine ⟨8034417533954295645830543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5356278355969530430553695 8034417533954295645830543)
    ·
      refine ⟨12051626300931443468745815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8034417533954295645830543 12051626300931443468745815)
      ·
        refine ⟨18077439451397165203118723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12051626300931443468745815 18077439451397165203118723)
        ·
          refine ⟨27116159177095747804678085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18077439451397165203118723 27116159177095747804678085)
          ·
            refine ⟨5084279845705452713377141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27116159177095747804678085 5084279845705452713377141)
            ·
              refine ⟨476651235534886191879107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5084279845705452713377141 476651235534886191879107)
              ·
                refine ⟨714976853302329287818661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476651235534886191879107 714976853302329287818661)
                ·
                  refine ⟨134058159994186741465999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 714976853302329287818661 134058159994186741465999)
                  ·
                    rfl

theorem cell20_293712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 4].length) (baseStart_293712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293712 prefixEnd_293712 := by exact prefixLift 293712
  have htrace : WordTrace (prefixWord ++ tailWord_293712) baseStart_293712 baseEnd_293712 := by
    simpa [prefixWord, tailWord_293712, baseEnd_293712] using wordTrace_append hprefix tailTrace_293712
  have hstable : (prefixWord ++ tailWord_293712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293712).length < 2 ^ (prefixWord ++ tailWord_293712).sum := by decide
  have hdescent : baseEnd_293712 < baseStart_293712 := by decide
  rcases family_descends (prefixWord ++ tailWord_293712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293719 : List Nat := [1, 1, 3, 2, 4, 1, 1, 7]
def baseStart_293719 : Nat := 118140960795 + 293719 * 2 ^ 59
def prefixEnd_293719 : Nat := 4983230072969 + 3 ^ 40 * 293719 * 2
def baseEnd_293719 : Nat := 44687118328308609410879

theorem tailTrace_293719 : CollatzResearch.WordTrace tailWord_293719 prefixEnd_293719 44687118328308609410879 := by
  unfold tailWord_293719
  simp only [CollatzResearch.WordTrace]
  refine ⟨10712812022913701056612211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7141874681942467371074807 10712812022913701056612211)
  ·
    refine ⟨16069218034370551584918317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10712812022913701056612211 16069218034370551584918317)
    ·
      refine ⟨6025956762888956844344369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16069218034370551584918317 6025956762888956844344369)
      ·
        refine ⟨4519467572166717633258277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6025956762888956844344369 4519467572166717633258277)
        ·
          refine ⟨847400169781259556235927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4519467572166717633258277 847400169781259556235927)
          ·
            refine ⟨1271100254671889334353891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847400169781259556235927 1271100254671889334353891)
            ·
              refine ⟨1906650382007834001530837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1271100254671889334353891 1906650382007834001530837)
              ·
                refine ⟨44687118328308609410879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1906650382007834001530837 44687118328308609410879)
                ·
                  rfl

theorem cell20_293719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 7].length) (baseStart_293719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293719 prefixEnd_293719 := by exact prefixLift 293719
  have htrace : WordTrace (prefixWord ++ tailWord_293719) baseStart_293719 baseEnd_293719 := by
    simpa [prefixWord, tailWord_293719, baseEnd_293719] using wordTrace_append hprefix tailTrace_293719
  have hstable : (prefixWord ++ tailWord_293719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293719).length < 2 ^ (prefixWord ++ tailWord_293719).sum := by decide
  have hdescent : baseEnd_293719 < baseStart_293719 := by decide
  rcases family_descends (prefixWord ++ tailWord_293719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293722 : List Nat := [3, 1, 1, 2, 1, 4, 4, 1, 3]
def baseStart_293722 : Nat := 118140960795 + 293722 * 2 ^ 59
def prefixEnd_293722 : Nat := 4983230072969 + 3 ^ 40 * 293722 * 2
def baseEnd_293722 : Nat := 134062724266671151132625

theorem tailTrace_293722 : CollatzResearch.WordTrace tailWord_293722 prefixEnd_293722 134062724266671151132625 := by
  unfold tailWord_293722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2678230360475708142242855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7141947627935221712647613 2678230360475708142242855)
  ·
    refine ⟨4017345540713562213364283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2678230360475708142242855 4017345540713562213364283)
    ·
      refine ⟨6026018311070343320046425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4017345540713562213364283 6026018311070343320046425)
      ·
        refine ⟨4519513733302757490034819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6026018311070343320046425 4519513733302757490034819)
        ·
          refine ⟨6779270599954136235052229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4519513733302757490034819 6779270599954136235052229)
          ·
            refine ⟨1271113237491400544072293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6779270599954136235052229 1271113237491400544072293)
            ·
              refine ⟨238333732029637602013555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1271113237491400544072293 238333732029637602013555)
              ·
                refine ⟨357500598044456403020333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238333732029637602013555 357500598044456403020333)
                ·
                  refine ⟨134062724266671151132625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357500598044456403020333 134062724266671151132625)
                  ·
                    rfl

theorem cell20_293722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_293722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293722 prefixEnd_293722 := by exact prefixLift 293722
  have htrace : WordTrace (prefixWord ++ tailWord_293722) baseStart_293722 baseEnd_293722 := by
    simpa [prefixWord, tailWord_293722, baseEnd_293722] using wordTrace_append hprefix tailTrace_293722
  have hstable : (prefixWord ++ tailWord_293722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293722).length < 2 ^ (prefixWord ++ tailWord_293722).sum := by decide
  have hdescent : baseEnd_293722 < baseStart_293722 := by decide
  rcases family_descends (prefixWord ++ tailWord_293722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293781 : List Nat := [1, 3, 2, 1, 1, 4, 2, 3, 3]
def baseStart_293781 : Nat := 118140960795 + 293781 * 2 ^ 59
def prefixEnd_293781 : Nat := 4983230072969 + 3 ^ 40 * 293781 * 2
def baseEnd_293781 : Nat := 134089653474329168165717

theorem tailTrace_293781 : CollatzResearch.WordTrace tailWord_293781 prefixEnd_293781 134089653474329168165717 := by
  unfold tailWord_293781
  simp only [CollatzResearch.WordTrace]
  refine ⟨10715073348689085645369197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7143382232459390430246131 10715073348689085645369197)
  ·
    refine ⟨4018152505758407117013449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10715073348689085645369197 4018152505758407117013449)
    ·
      refine ⟨3013614379318805337760087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4018152505758407117013449 3013614379318805337760087)
      ·
        refine ⟨4520421568978208006640131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3013614379318805337760087 4520421568978208006640131)
        ·
          refine ⟨6780632353467312009960197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4520421568978208006640131 6780632353467312009960197)
          ·
            refine ⟨1271368566275121001867537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6780632353467312009960197 1271368566275121001867537)
            ·
              refine ⟨953526424706340751400653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1271368566275121001867537 953526424706340751400653)
              ·
                refine ⟨357572409264877781775245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 953526424706340751400653 357572409264877781775245)
                ·
                  refine ⟨134089653474329168165717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357572409264877781775245 134089653474329168165717)
                  ·
                    rfl

theorem cell20_293781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_293781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293781 prefixEnd_293781 := by exact prefixLift 293781
  have htrace : WordTrace (prefixWord ++ tailWord_293781) baseStart_293781 baseEnd_293781 := by
    simpa [prefixWord, tailWord_293781, baseEnd_293781] using wordTrace_append hprefix tailTrace_293781
  have hstable : (prefixWord ++ tailWord_293781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293781).length < 2 ^ (prefixWord ++ tailWord_293781).sum := by decide
  have hdescent : baseEnd_293781 < baseStart_293781 := by decide
  rcases family_descends (prefixWord ++ tailWord_293781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293836 : List Nat := [2, 2, 1, 4, 1, 1, 5, 1, 3]
def baseStart_293836 : Nat := 118140960795 + 293836 * 2 ^ 59
def prefixEnd_293836 : Nat := 4983230072969 + 3 ^ 40 * 293836 * 2
def baseEnd_293836 : Nat := 134114756972993421332159

theorem tailTrace_293836 : CollatzResearch.WordTrace tailWord_293836 prefixEnd_293836 134114756972993421332159 := by
  unfold tailWord_293836
  simp only [CollatzResearch.WordTrace]
  refine ⟨5358539681744915019310681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7144719575659886692414241 5358539681744915019310681)
  ·
    refine ⟨4018904761308686264483011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5358539681744915019310681 4018904761308686264483011)
    ·
      refine ⟨6028357141963029396724517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4018904761308686264483011 6028357141963029396724517)
      ·
        refine ⟨1130316964118068011885847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6028357141963029396724517 1130316964118068011885847)
        ·
          refine ⟨1695475446177102017828771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130316964118068011885847 1695475446177102017828771)
          ·
            refine ⟨2543213169265653026743157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695475446177102017828771 2543213169265653026743157)
            ·
              refine ⟨238426234618654971257171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2543213169265653026743157 238426234618654971257171)
              ·
                refine ⟨357639351927982456885757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238426234618654971257171 357639351927982456885757)
                ·
                  refine ⟨134114756972993421332159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357639351927982456885757 134114756972993421332159)
                  ·
                    rfl

theorem cell20_293836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_293836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293836 prefixEnd_293836 := by exact prefixLift 293836
  have htrace : WordTrace (prefixWord ++ tailWord_293836) baseStart_293836 baseEnd_293836 := by
    simpa [prefixWord, tailWord_293836, baseEnd_293836] using wordTrace_append hprefix tailTrace_293836
  have hstable : (prefixWord ++ tailWord_293836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293836).length < 2 ^ (prefixWord ++ tailWord_293836).sum := by decide
  have hdescent : baseEnd_293836 < baseStart_293836 := by decide
  rcases family_descends (prefixWord ++ tailWord_293836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293846 : List Nat := [5, 2, 1, 1, 2, 3, 2, 4]
def baseStart_293846 : Nat := 118140960795 + 293846 * 2 ^ 59
def prefixEnd_293846 : Nat := 4983230072969 + 3 ^ 40 * 293846 * 2
def baseEnd_293846 : Nat := 44706440415159276999595

theorem tailTrace_293846 : CollatzResearch.WordTrace tailWord_293846 prefixEnd_293846 44706440415159276999595 := by
  unfold tailWord_293846
  simp only [CollatzResearch.WordTrace]
  refine ⟨669840255840850109155337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7144962728969067830990261 669840255840850109155337)
  ·
    refine ⟨502380191880637581866503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 669840255840850109155337 502380191880637581866503)
    ·
      refine ⟨753570287820956372799755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502380191880637581866503 753570287820956372799755)
      ·
        refine ⟨1130355431731434559199633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 753570287820956372799755 1130355431731434559199633)
        ·
          refine ⟨847766573798575919399725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1130355431731434559199633 847766573798575919399725)
          ·
            refine ⟨317912465174465969774897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 847766573798575919399725 317912465174465969774897)
            ·
              refine ⟨238434348880849477331173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317912465174465969774897 238434348880849477331173)
              ·
                refine ⟨44706440415159276999595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 238434348880849477331173 44706440415159276999595)
                ·
                  rfl

theorem cell20_293846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_293846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293846 prefixEnd_293846 := by exact prefixLift 293846
  have htrace : WordTrace (prefixWord ++ tailWord_293846) baseStart_293846 baseEnd_293846 := by
    simpa [prefixWord, tailWord_293846, baseEnd_293846] using wordTrace_append hprefix tailTrace_293846
  have hstable : (prefixWord ++ tailWord_293846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293846).length < 2 ^ (prefixWord ++ tailWord_293846).sum := by decide
  have hdescent : baseEnd_293846 < baseStart_293846 := by decide
  rcases family_descends (prefixWord ++ tailWord_293846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293847 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 6]
def baseStart_293847 : Nat := 118140960795 + 293847 * 2 ^ 59
def prefixEnd_293847 : Nat := 4983230072969 + 3 ^ 40 * 293847 * 2
def baseEnd_293847 : Nat := 134119777672726271965447

theorem tailTrace_293847 : CollatzResearch.WordTrace tailWord_293847 prefixEnd_293847 134119777672726271965447 := by
  unfold tailWord_293847
  simp only [CollatzResearch.WordTrace]
  refine ⟨10717480566449978917271795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7144987044299985944847863 10717480566449978917271795)
  ·
    refine ⟨16076220849674968375907693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10717480566449978917271795 16076220849674968375907693)
    ·
      refine ⟨6028582818628113140965385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16076220849674968375907693 6028582818628113140965385)
      ·
        refine ⟨4521437113971084855724039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6028582818628113140965385 4521437113971084855724039)
        ·
          refine ⟨6782155670956627283586059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4521437113971084855724039 6782155670956627283586059)
          ·
            refine ⟨10173233506434940925379089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6782155670956627283586059 10173233506434940925379089)
            ·
              refine ⟨7629925129826205694034317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10173233506434940925379089 7629925129826205694034317)
              ·
                refine ⟨2861221923684827135262869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7629925129826205694034317 2861221923684827135262869)
                ·
                  refine ⟨134119777672726271965447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2861221923684827135262869 134119777672726271965447)
                  ·
                    rfl

theorem cell20_293847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_293847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293847 prefixEnd_293847 := by exact prefixLift 293847
  have htrace : WordTrace (prefixWord ++ tailWord_293847) baseStart_293847 baseEnd_293847 := by
    simpa [prefixWord, tailWord_293847, baseEnd_293847] using wordTrace_append hprefix tailTrace_293847
  have hstable : (prefixWord ++ tailWord_293847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293847).length < 2 ^ (prefixWord ++ tailWord_293847).sum := by decide
  have hdescent : baseEnd_293847 < baseStart_293847 := by decide
  rcases family_descends (prefixWord ++ tailWord_293847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293850 : List Nat := [3, 1, 1, 2, 4, 1, 4, 4]
def baseStart_293850 : Nat := 118140960795 + 293850 * 2 ^ 59
def prefixEnd_293850 : Nat := 4983230072969 + 3 ^ 40 * 293850 * 2
def baseEnd_293850 : Nat := 44707048984823864955145

theorem tailTrace_293850 : CollatzResearch.WordTrace tailWord_293850 prefixEnd_293850 44707048984823864955145 := by
  unfold tailWord_293850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2679397496359777607407751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7145059990292740286420669 2679397496359777607407751)
  ·
    refine ⟨4019096244539666411111627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2679397496359777607407751 4019096244539666411111627)
    ·
      refine ⟨6028644366809499616667441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4019096244539666411111627 6028644366809499616667441)
      ·
        refine ⟨4521483275107124712500581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6028644366809499616667441 4521483275107124712500581)
        ·
          refine ⟨847778114082585883593859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4521483275107124712500581 847778114082585883593859)
          ·
            refine ⟨1271667171123878825390789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847778114082585883593859 1271667171123878825390789)
            ·
              refine ⟨238437594585727279760773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1271667171123878825390789 238437594585727279760773)
              ·
                refine ⟨44707048984823864955145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 238437594585727279760773 44707048984823864955145)
                ·
                  rfl

theorem cell20_293850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_293850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293850 prefixEnd_293850 := by exact prefixLift 293850
  have htrace : WordTrace (prefixWord ++ tailWord_293850) baseStart_293850 baseEnd_293850 := by
    simpa [prefixWord, tailWord_293850, baseEnd_293850] using wordTrace_append hprefix tailTrace_293850
  have hstable : (prefixWord ++ tailWord_293850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293850).length < 2 ^ (prefixWord ++ tailWord_293850).sum := by decide
  have hdescent : baseEnd_293850 < baseStart_293850 := by decide
  rcases family_descends (prefixWord ++ tailWord_293850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293871 : List Nat := [1, 1, 2, 1, 4, 5, 6]
def baseStart_293871 : Nat := 118140960795 + 293871 * 2 ^ 59
def prefixEnd_293871 : Nat := 4983230072969 + 3 ^ 40 * 293871 * 2
def baseEnd_293871 : Nat := 14903414658520983907261

theorem tailTrace_293871 : CollatzResearch.WordTrace tailWord_293871 prefixEnd_293871 14903414658520983907261 := by
  unfold tailWord_293871
  simp only [CollatzResearch.WordTrace]
  refine ⟨10718355918363031016145467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7145570612242020677430311 10718355918363031016145467)
  ·
    refine ⟨16077533877544546524218201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10718355918363031016145467 16077533877544546524218201)
    ·
      refine ⟨12058150408158409893163651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16077533877544546524218201 12058150408158409893163651)
      ·
        refine ⟨18087225612237614839745477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12058150408158409893163651 18087225612237614839745477)
        ·
          refine ⟨3391354802294552782452277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18087225612237614839745477 3391354802294552782452277)
          ·
            refine ⟨317939512715114323354901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3391354802294552782452277 317939512715114323354901)
            ·
              refine ⟨14903414658520983907261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 317939512715114323354901 14903414658520983907261)
              ·
                rfl

theorem cell20_293871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 6].length) (baseStart_293871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293871 prefixEnd_293871 := by exact prefixLift 293871
  have htrace : WordTrace (prefixWord ++ tailWord_293871) baseStart_293871 baseEnd_293871 := by
    simpa [prefixWord, tailWord_293871, baseEnd_293871] using wordTrace_append hprefix tailTrace_293871
  have hstable : (prefixWord ++ tailWord_293871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293871).length < 2 ^ (prefixWord ++ tailWord_293871).sum := by decide
  have hdescent : baseEnd_293871 < baseStart_293871 := by decide
  rcases family_descends (prefixWord ++ tailWord_293871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293877 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 4]
def baseStart_293877 : Nat := 118140960795 + 293877 * 2 ^ 59
def prefixEnd_293877 : Nat := 4983230072969 + 3 ^ 40 * 293877 * 2
def baseEnd_293877 : Nat := 134133470490179500965325

theorem tailTrace_293877 : CollatzResearch.WordTrace tailWord_293877 prefixEnd_293877 134133470490179500965325 := by
  unfold tailWord_293877
  simp only [CollatzResearch.WordTrace]
  refine ⟨10718574756341294040863885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7145716504227529360575923 10718574756341294040863885)
  ·
    refine ⟨4019465533627985265323957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10718574756341294040863885 4019465533627985265323957)
    ·
      refine ⟨376824893777623618624121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4019465533627985265323957 376824893777623618624121)
      ·
        refine ⟨282618670333217713968091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 376824893777623618624121 282618670333217713968091)
        ·
          refine ⟨423928005499826570952137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282618670333217713968091 423928005499826570952137)
          ·
            refine ⟨317946004124869928214103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 423928005499826570952137 317946004124869928214103)
            ·
              refine ⟨476919006187304892321155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317946004124869928214103 476919006187304892321155)
              ·
                refine ⟨715378509280957338481733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 476919006187304892321155 715378509280957338481733)
                ·
                  refine ⟨134133470490179500965325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 715378509280957338481733 134133470490179500965325)
                  ·
                    rfl

theorem cell20_293877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_293877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293877 prefixEnd_293877 := by exact prefixLift 293877
  have htrace : WordTrace (prefixWord ++ tailWord_293877) baseStart_293877 baseEnd_293877 := by
    simpa [prefixWord, tailWord_293877, baseEnd_293877] using wordTrace_append hprefix tailTrace_293877
  have hstable : (prefixWord ++ tailWord_293877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293877).length < 2 ^ (prefixWord ++ tailWord_293877).sum := by decide
  have hdescent : baseEnd_293877 < baseStart_293877 := by decide
  rcases family_descends (prefixWord ++ tailWord_293877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293895 : List Nat := [1, 1, 4, 3, 1, 1, 3, 3, 3]
def baseStart_293895 : Nat := 118140960795 + 293895 * 2 ^ 59
def prefixEnd_293895 : Nat := 4983230072969 + 3 ^ 40 * 293895 * 2
def baseEnd_293895 : Nat := 134141686180651438365251

theorem tailTrace_293895 : CollatzResearch.WordTrace tailWord_293895 prefixEnd_293895 134141686180651438365251 := by
  unfold tailWord_293895
  simp only [CollatzResearch.WordTrace]
  refine ⟨10719231270276083115019139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7146154180184055410012759 10719231270276083115019139)
  ·
    refine ⟨16078846905414124672528709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10719231270276083115019139 16078846905414124672528709)
    ·
      refine ⟨3014783794765148376099133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16078846905414124672528709 3014783794765148376099133)
      ·
        refine ⟨1130543923036930641037175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3014783794765148376099133 1130543923036930641037175)
        ·
          refine ⟨1695815884555395961555763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130543923036930641037175 1695815884555395961555763)
          ·
            refine ⟨2543723826833093942333645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1695815884555395961555763 2543723826833093942333645)
            ·
              refine ⟨953896435062410228375117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2543723826833093942333645 953896435062410228375117)
              ·
                refine ⟨357711163148403835640669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 953896435062410228375117 357711163148403835640669)
                ·
                  refine ⟨134141686180651438365251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357711163148403835640669 134141686180651438365251)
                  ·
                    rfl

theorem cell20_293895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 3].length) (baseStart_293895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293895 prefixEnd_293895 := by exact prefixLift 293895
  have htrace : WordTrace (prefixWord ++ tailWord_293895) baseStart_293895 baseEnd_293895 := by
    simpa [prefixWord, tailWord_293895, baseEnd_293895] using wordTrace_append hprefix tailTrace_293895
  have hstable : (prefixWord ++ tailWord_293895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293895).length < 2 ^ (prefixWord ++ tailWord_293895).sum := by decide
  have hdescent : baseEnd_293895 < baseStart_293895 := by decide
  rcases family_descends (prefixWord ++ tailWord_293895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293909 : List Nat := [1, 3, 2, 1, 4, 1, 2, 6]
def baseStart_293909 : Nat := 118140960795 + 293909 * 2 ^ 59
def prefixEnd_293909 : Nat := 4983230072969 + 3 ^ 40 * 293909 * 2
def baseEnd_293909 : Nat := 44716025387376537299509

theorem tailTrace_293909 : CollatzResearch.WordTrace tailWord_293909 prefixEnd_293909 44716025387376537299509 := by
  unfold tailWord_293909
  simp only [CollatzResearch.WordTrace]
  refine ⟨10719741892225363506028781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7146494594816909004019187 10719741892225363506028781)
  ·
    refine ⟨4019903209584511314760793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10719741892225363506028781 4019903209584511314760793)
    ·
      refine ⟨3014927407188383486070595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4019903209584511314760793 3014927407188383486070595)
      ·
        refine ⟨4522391110782575229105893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3014927407188383486070595 4522391110782575229105893)
        ·
          refine ⟨847948333271732855457355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4522391110782575229105893 847948333271732855457355)
          ·
            refine ⟨1271922499907599283186033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847948333271732855457355 1271922499907599283186033)
            ·
              refine ⟨953941874930699462389525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1271922499907599283186033 953941874930699462389525)
              ·
                refine ⟨44716025387376537299509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 953941874930699462389525 44716025387376537299509)
                ·
                  rfl

theorem cell20_293909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 6].length) (baseStart_293909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293909 prefixEnd_293909 := by exact prefixLift 293909
  have htrace : WordTrace (prefixWord ++ tailWord_293909) baseStart_293909 baseEnd_293909 := by
    simpa [prefixWord, tailWord_293909, baseEnd_293909] using wordTrace_append hprefix tailTrace_293909
  have hstable : (prefixWord ++ tailWord_293909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293909).length < 2 ^ (prefixWord ++ tailWord_293909).sum := by decide
  have hdescent : baseEnd_293909 < baseStart_293909 := by decide
  rcases family_descends (prefixWord ++ tailWord_293909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293950 : List Nat := [4, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_293950 : Nat := 118140960795 + 293950 * 2 ^ 59
def prefixEnd_293950 : Nat := 4983230072969 + 3 ^ 40 * 293950 * 2
def baseEnd_293950 : Nat := 134166789679315691531693

theorem tailTrace_293950 : CollatzResearch.WordTrace tailWord_293950 prefixEnd_293950 134166789679315691531693 := by
  unfold tailWord_293950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1340154660634603438533913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7147491523384551672180869 1340154660634603438533913)
  ·
    refine ⟨1005115995475952578900435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1340154660634603438533913 1005115995475952578900435)
    ·
      refine ⟨1507673993213928868350653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1005115995475952578900435 1507673993213928868350653)
      ·
        refine ⟨565377747455223325631495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1507673993213928868350653 565377747455223325631495)
        ·
          refine ⟨848066621182834988447243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565377747455223325631495 848066621182834988447243)
          ·
            refine ⟨1272099931774252482670865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848066621182834988447243 1272099931774252482670865)
            ·
              refine ⟨954074948830689362003149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1272099931774252482670865 954074948830689362003149)
              ·
                refine ⟨357778105811508510751181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 954074948830689362003149 357778105811508510751181)
                ·
                  refine ⟨134166789679315691531693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 357778105811508510751181 134166789679315691531693)
                  ·
                    rfl

theorem cell20_293950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_293950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293950 prefixEnd_293950 := by exact prefixLift 293950
  have htrace : WordTrace (prefixWord ++ tailWord_293950) baseStart_293950 baseEnd_293950 := by
    simpa [prefixWord, tailWord_293950, baseEnd_293950] using wordTrace_append hprefix tailTrace_293950
  have hstable : (prefixWord ++ tailWord_293950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293950).length < 2 ^ (prefixWord ++ tailWord_293950).sum := by decide
  have hdescent : baseEnd_293950 < baseStart_293950 := by decide
  rcases family_descends (prefixWord ++ tailWord_293950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_293968 : List Nat := [2, 1, 1, 1, 1, 3, 1, 10]
def baseStart_293968 : Nat := 118140960795 + 293968 * 2 ^ 59
def prefixEnd_293968 : Nat := 4983230072969 + 3 ^ 40 * 293968 * 2
def baseEnd_293968 : Nat := 44725001789929209643873

theorem tailTrace_293968 : CollatzResearch.WordTrace tailWord_293968 prefixEnd_293968 44725001789929209643873 := by
  unfold tailWord_293968
  simp only [CollatzResearch.WordTrace]
  refine ⟨5360946899505808291213279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7147929199341077721617705 5360946899505808291213279)
  ·
    refine ⟨8041420349258712436819919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5360946899505808291213279 8041420349258712436819919)
    ·
      refine ⟨12062130523888068655229879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8041420349258712436819919 12062130523888068655229879)
      ·
        refine ⟨18093195785832102982844819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12062130523888068655229879 18093195785832102982844819)
        ·
          refine ⟨27139793678748154474267229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18093195785832102982844819 27139793678748154474267229)
          ·
            refine ⟨10177422629530557927850211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27139793678748154474267229 10177422629530557927850211)
            ·
              refine ⟨15266133944295836891775317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10177422629530557927850211 15266133944295836891775317)
              ·
                refine ⟨44725001789929209643873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15266133944295836891775317 44725001789929209643873)
                ·
                  rfl

theorem cell20_293968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_293968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_293968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_293968 prefixEnd_293968 := by exact prefixLift 293968
  have htrace : WordTrace (prefixWord ++ tailWord_293968) baseStart_293968 baseEnd_293968 := by
    simpa [prefixWord, tailWord_293968, baseEnd_293968] using wordTrace_append hprefix tailTrace_293968
  have hstable : (prefixWord ++ tailWord_293968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_293968).length < 2 ^ (prefixWord ++ tailWord_293968).sum := by decide
  have hdescent : baseEnd_293968 < baseStart_293968 := by decide
  rcases family_descends (prefixWord ++ tailWord_293968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294050 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 4]
def baseStart_294050 : Nat := 118140960795 + 294050 * 2 ^ 59
def prefixEnd_294050 : Nat := 4983230072969 + 3 ^ 40 * 294050 * 2
def baseEnd_294050 : Nat := 134212432404159788197951

theorem tailTrace_294050 : CollatzResearch.WordTrace tailWord_294050 prefixEnd_294050 134212432404159788197951 := by
  unfold tailWord_294050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2681221146178636146727901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7149923056476363057941069 2681221146178636146727901)
  ·
    refine ⟨1005457929816988555022963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2681221146178636146727901 1005457929816988555022963)
    ·
      refine ⟨1508186894725482832534445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1005457929816988555022963 1508186894725482832534445)
      ·
        refine ⟨565570085522056062200417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1508186894725482832534445 565570085522056062200417)
        ·
          refine ⟨424177564141542046650313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 565570085522056062200417 424177564141542046650313)
          ·
            refine ⟨318133173106156534987735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424177564141542046650313 318133173106156534987735)
            ·
              refine ⟨477199759659234802481603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318133173106156534987735 477199759659234802481603)
              ·
                refine ⟨715799639488852203722405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 477199759659234802481603 715799639488852203722405)
                ·
                  refine ⟨134212432404159788197951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 715799639488852203722405 134212432404159788197951)
                  ·
                    rfl

theorem cell20_294050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_294050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294050 prefixEnd_294050 := by exact prefixLift 294050
  have htrace : WordTrace (prefixWord ++ tailWord_294050) baseStart_294050 baseEnd_294050 := by
    simpa [prefixWord, tailWord_294050, baseEnd_294050] using wordTrace_append hprefix tailTrace_294050
  have hstable : (prefixWord ++ tailWord_294050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294050).length < 2 ^ (prefixWord ++ tailWord_294050).sum := by decide
  have hdescent : baseEnd_294050 < baseStart_294050 := by decide
  rcases family_descends (prefixWord ++ tailWord_294050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294137 : List Nat := [1, 2, 1, 3, 1, 1, 7, 4]
def baseStart_294137 : Nat := 118140960795 + 294137 * 2 ^ 59
def prefixEnd_294137 : Nat := 4983230072969 + 3 ^ 40 * 294137 * 2
def baseEnd_294137 : Nat := 44750713858258050765865

theorem tailTrace_294137 : CollatzResearch.WordTrace tailWord_294137 prefixEnd_294137 44750713858258050765865 := by
  unfold tailWord_294137
  simp only [CollatzResearch.WordTrace]
  refine ⟨10728057735399358445328665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7152038490266238963552443 10728057735399358445328665)
  ·
    refine ⟨8046043301549518833996499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10728057735399358445328665 8046043301549518833996499)
    ·
      refine ⟨12069064952324278250994749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8046043301549518833996499 12069064952324278250994749)
      ·
        refine ⟨4525899357121604344123031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12069064952324278250994749 4525899357121604344123031)
        ·
          refine ⟨6788849035682406516184547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4525899357121604344123031 6788849035682406516184547)
          ·
            refine ⟨10183273553523609774276821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6788849035682406516184547 10183273553523609774276821)
            ·
              refine ⟨238670473910709604084613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10183273553523609774276821 238670473910709604084613)
              ·
                refine ⟨44750713858258050765865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 238670473910709604084613 44750713858258050765865)
                ·
                  rfl

theorem cell20_294137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 4].length) (baseStart_294137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294137 prefixEnd_294137 := by exact prefixLift 294137
  have htrace : WordTrace (prefixWord ++ tailWord_294137) baseStart_294137 baseEnd_294137 := by
    simpa [prefixWord, tailWord_294137, baseEnd_294137] using wordTrace_append hprefix tailTrace_294137
  have hstable : (prefixWord ++ tailWord_294137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294137).length < 2 ^ (prefixWord ++ tailWord_294137).sum := by decide
  have hdescent : baseEnd_294137 < baseStart_294137 := by decide
  rcases family_descends (prefixWord ++ tailWord_294137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294147 : List Nat := [1, 1, 1, 3, 2, 5, 2, 3, 2]
def baseStart_294147 : Nat := 118140960795 + 294147 * 2 ^ 59
def prefixEnd_294147 : Nat := 4983230072969 + 3 ^ 40 * 294147 * 2
def baseEnd_294147 : Nat := 134256705847258561964221

theorem tailTrace_294147 : CollatzResearch.WordTrace tailWord_294147 prefixEnd_294147 134256705847258561964221 := by
  unfold tailWord_294147
  simp only [CollatzResearch.WordTrace]
  refine ⟨10728422465363130153192695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7152281643575420102128463 10728422465363130153192695)
  ·
    refine ⟨16092633698044695229789043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10728422465363130153192695 16092633698044695229789043)
    ·
      refine ⟨24138950547067042844683565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16092633698044695229789043 24138950547067042844683565)
      ·
        refine ⟨9052106455150141066756337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24138950547067042844683565 9052106455150141066756337)
        ·
          refine ⟨6789079841362605800067253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9052106455150141066756337 6789079841362605800067253)
          ·
            refine ⟨636476235127744293756305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6789079841362605800067253 636476235127744293756305)
            ·
              refine ⟨477357176345808220317229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636476235127744293756305 477357176345808220317229)
              ·
                refine ⟨179008941129678082618961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 477357176345808220317229 179008941129678082618961)
                ·
                  refine ⟨134256705847258561964221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179008941129678082618961 134256705847258561964221)
                  ·
                    rfl

theorem cell20_294147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 2].length) (baseStart_294147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294147 prefixEnd_294147 := by exact prefixLift 294147
  have htrace : WordTrace (prefixWord ++ tailWord_294147) baseStart_294147 baseEnd_294147 := by
    simpa [prefixWord, tailWord_294147, baseEnd_294147] using wordTrace_append hprefix tailTrace_294147
  have hstable : (prefixWord ++ tailWord_294147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294147).length < 2 ^ (prefixWord ++ tailWord_294147).sum := by decide
  have hdescent : baseEnd_294147 < baseStart_294147 := by decide
  rcases family_descends (prefixWord ++ tailWord_294147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294168 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 4]
def baseStart_294168 : Nat := 118140960795 + 294168 * 2 ^ 59
def prefixEnd_294168 : Nat := 4983230072969 + 3 ^ 40 * 294168 * 2
def baseEnd_294168 : Nat := 134266290819475822264135

theorem tailTrace_294168 : CollatzResearch.WordTrace tailWord_294168 prefixEnd_294168 134266290819475822264135 := by
  unfold tailWord_294168
  simp only [CollatzResearch.WordTrace]
  refine ⟨5364594199143525369853579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7152792265524700493138105 5364594199143525369853579)
  ·
    refine ⟨8046891298715288054780369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5364594199143525369853579 8046891298715288054780369)
    ·
      refine ⟨6035168474036466041085277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8046891298715288054780369 6035168474036466041085277)
      ·
        refine ⟨2263188177763674765406979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6035168474036466041085277 2263188177763674765406979)
        ·
          refine ⟨3394782266645512148110469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263188177763674765406979 3394782266645512148110469)
          ·
            refine ⟨636521674996033527770713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3394782266645512148110469 636521674996033527770713)
            ·
              refine ⟨477391256247025145828035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636521674996033527770713 477391256247025145828035)
              ·
                refine ⟨716086884370537718742053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 477391256247025145828035 716086884370537718742053)
                ·
                  refine ⟨134266290819475822264135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 716086884370537718742053 134266290819475822264135)
                  ·
                    rfl

theorem cell20_294168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_294168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294168 prefixEnd_294168 := by exact prefixLift 294168
  have htrace : WordTrace (prefixWord ++ tailWord_294168) baseStart_294168 baseEnd_294168 := by
    simpa [prefixWord, tailWord_294168, baseEnd_294168] using wordTrace_append hprefix tailTrace_294168
  have hstable : (prefixWord ++ tailWord_294168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294168).length < 2 ^ (prefixWord ++ tailWord_294168).sum := by decide
  have hdescent : baseEnd_294168 < baseStart_294168 := by decide
  rcases family_descends (prefixWord ++ tailWord_294168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294174 : List Nat := [4, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_294174 : Nat := 118140960795 + 294174 * 2 ^ 59
def prefixEnd_294174 : Nat := 4983230072969 + 3 ^ 40 * 294174 * 2
def baseEnd_294174 : Nat := 134269029382966468064111

theorem tailTrace_294174 : CollatzResearch.WordTrace tailWord_294174 prefixEnd_294174 134269029382966468064111 := by
  unfold tailWord_294174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1341175904533164220553197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7152938157510209176283717 1341175904533164220553197)
  ·
    refine ⟨502940964199936582707449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1341175904533164220553197 502940964199936582707449)
    ·
      refine ⟨377205723149952437030587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 502940964199936582707449 377205723149952437030587)
      ·
        refine ⟨565808584724928655545881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377205723149952437030587 565808584724928655545881)
        ·
          refine ⟨424356438543696491659411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 565808584724928655545881 424356438543696491659411)
          ·
            refine ⟨636534657815544737489117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424356438543696491659411 636534657815544737489117)
            ·
              refine ⟨238700496680829276558419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 636534657815544737489117 238700496680829276558419)
              ·
                refine ⟨358050745021243914837629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238700496680829276558419 358050745021243914837629)
                ·
                  refine ⟨134269029382966468064111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 358050745021243914837629 134269029382966468064111)
                  ·
                    rfl

theorem cell20_294174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_294174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294174 prefixEnd_294174 := by exact prefixLift 294174
  have htrace : WordTrace (prefixWord ++ tailWord_294174) baseStart_294174 baseEnd_294174 := by
    simpa [prefixWord, tailWord_294174, baseEnd_294174] using wordTrace_append hprefix tailTrace_294174
  have hstable : (prefixWord ++ tailWord_294174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294174).length < 2 ^ (prefixWord ++ tailWord_294174).sum := by decide
  have hdescent : baseEnd_294174 < baseStart_294174 := by decide
  rcases family_descends (prefixWord ++ tailWord_294174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294198 : List Nat := [5, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_294198 : Nat := 118140960795 + 294198 * 2 ^ 59
def prefixEnd_294198 : Nat := 4983230072969 + 3 ^ 40 * 294198 * 2
def baseEnd_294198 : Nat := 134279983636929051264013

theorem tailTrace_294198 : CollatzResearch.WordTrace tailWord_294198 prefixEnd_294198 134279983636929051264013 := by
  unfold tailWord_294198
  simp only [CollatzResearch.WordTrace]
  refine ⟨670642661761147866456203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7153521725452243908866165 670642661761147866456203)
  ·
    refine ⟨1005963992641721799684305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 670642661761147866456203 1005963992641721799684305)
    ·
      refine ⟨754472994481291349763229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1005963992641721799684305 754472994481291349763229)
      ·
        refine ⟨282927372930484256161211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 754472994481291349763229 282927372930484256161211)
        ·
          refine ⟨424391059395726384241817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282927372930484256161211 424391059395726384241817)
          ·
            refine ⟨318293294546794788181363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424391059395726384241817 318293294546794788181363)
            ·
              refine ⟨477439941820192182272045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318293294546794788181363 477439941820192182272045)
              ·
                refine ⟨179039978182572068352017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 477439941820192182272045 179039978182572068352017)
                ·
                  refine ⟨134279983636929051264013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179039978182572068352017 134279983636929051264013)
                  ·
                    rfl

theorem cell20_294198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_294198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294198 prefixEnd_294198 := by exact prefixLift 294198
  have htrace : WordTrace (prefixWord ++ tailWord_294198) baseStart_294198 baseEnd_294198 := by
    simpa [prefixWord, tailWord_294198, baseEnd_294198] using wordTrace_append hprefix tailTrace_294198
  have hstable : (prefixWord ++ tailWord_294198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294198).length < 2 ^ (prefixWord ++ tailWord_294198).sum := by decide
  have hdescent : baseEnd_294198 < baseStart_294198 := by decide
  rcases family_descends (prefixWord ++ tailWord_294198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294220 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 5]
def baseStart_294220 : Nat := 118140960795 + 294220 * 2 ^ 59
def prefixEnd_294220 : Nat := 4983230072969 + 3 ^ 40 * 294220 * 2
def baseEnd_294220 : Nat := 134290025036394752530589

theorem tailTrace_294220 : CollatzResearch.WordTrace tailWord_294220 prefixEnd_294220 134290025036394752530589 := by
  unfold tailWord_294220
  simp only [CollatzResearch.WordTrace]
  refine ⟨5365542497049331810300057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7154056662732442413733409 5365542497049331810300057)
  ·
    refine ⟨4024156872786998857725043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5365542497049331810300057 4024156872786998857725043)
    ·
      refine ⟨6036235309180498286587565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4024156872786998857725043 6036235309180498286587565)
      ·
        refine ⟨2263588240942686857470337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6036235309180498286587565 2263588240942686857470337)
        ·
          refine ⟨1697691180707015143102753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2263588240942686857470337 1697691180707015143102753)
          ·
            refine ⟨1273268385530261357327065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1697691180707015143102753 1273268385530261357327065)
            ·
              refine ⟨954951289147696017995299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1273268385530261357327065 954951289147696017995299)
              ·
                refine ⟨1432426933721544026992949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 954951289147696017995299 1432426933721544026992949)
                ·
                  refine ⟨134290025036394752530589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1432426933721544026992949 134290025036394752530589)
                  ·
                    rfl

theorem cell20_294220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_294220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294220 prefixEnd_294220 := by exact prefixLift 294220
  have htrace : WordTrace (prefixWord ++ tailWord_294220) baseStart_294220 baseEnd_294220 := by
    simpa [prefixWord, tailWord_294220, baseEnd_294220] using wordTrace_append hprefix tailTrace_294220
  have hstable : (prefixWord ++ tailWord_294220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294220).length < 2 ^ (prefixWord ++ tailWord_294220).sum := by decide
  have hdescent : baseEnd_294220 < baseStart_294220 := by decide
  rcases family_descends (prefixWord ++ tailWord_294220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294234 : List Nat := [3, 1, 1, 2, 1, 2, 3, 7]
def baseStart_294234 : Nat := 118140960795 + 294234 * 2 ^ 59
def prefixEnd_294234 : Nat := 4983230072969 + 3 ^ 40 * 294234 * 2
def baseEnd_294234 : Nat := 44765471672624308687955

theorem tailTrace_294234 : CollatzResearch.WordTrace tailWord_294234 prefixEnd_294234 44765471672624308687955 := by
  unfold tailWord_294234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2682898904011986002902439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7154397077365296007739837 2682898904011986002902439)
  ·
    refine ⟨4024348356017979004353659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2682898904011986002902439 4024348356017979004353659)
    ·
      refine ⟨6036522534026968506530489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4024348356017979004353659 6036522534026968506530489)
      ·
        refine ⟨4527391900520226379897867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6036522534026968506530489 4527391900520226379897867)
        ·
          refine ⟨6791087850780339569846801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4527391900520226379897867 6791087850780339569846801)
          ·
            refine ⟨5093315888085254677385101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6791087850780339569846801 5093315888085254677385101)
            ·
              refine ⟨1909993458031970504019413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5093315888085254677385101 1909993458031970504019413)
              ·
                refine ⟨44765471672624308687955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1909993458031970504019413 44765471672624308687955)
                ·
                  rfl

theorem cell20_294234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_294234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294234 prefixEnd_294234 := by exact prefixLift 294234
  have htrace : WordTrace (prefixWord ++ tailWord_294234) baseStart_294234 baseEnd_294234 := by
    simpa [prefixWord, tailWord_294234, baseEnd_294234] using wordTrace_append hprefix tailTrace_294234
  have hstable : (prefixWord ++ tailWord_294234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294234).length < 2 ^ (prefixWord ++ tailWord_294234).sum := by decide
  have hdescent : baseEnd_294234 < baseStart_294234 := by decide
  rcases family_descends (prefixWord ++ tailWord_294234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294274 : List Nat := [3, 4, 2, 1, 1, 3, 2, 2, 2]
def baseStart_294274 : Nat := 118140960795 + 294274 * 2 ^ 59
def prefixEnd_294274 : Nat := 4983230072969 + 3 ^ 40 * 294274 * 2
def baseEnd_294274 : Nat := 134314672107810564730369

theorem tailTrace_294274 : CollatzResearch.WordTrace tailWord_294274 prefixEnd_294274 134314672107810564730369 := by
  unfold tailWord_294274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2683263633975757710766469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7155369690602020562043917 2683263633975757710766469)
  ·
    refine ⟨503111931370454570768713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2683263633975757710766469 503111931370454570768713)
    ·
      refine ⟨377333948527840928076535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 503111931370454570768713 377333948527840928076535)
      ·
        refine ⟨566000922791761392114803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377333948527840928076535 566000922791761392114803)
        ·
          refine ⟨849001384187642088172205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566000922791761392114803 849001384187642088172205)
          ·
            refine ⟨318375519070365783064577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 849001384187642088172205 318375519070365783064577)
            ·
              refine ⟨238781639302774337298433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318375519070365783064577 238781639302774337298433)
              ·
                refine ⟨179086229477080752973825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238781639302774337298433 179086229477080752973825)
                ·
                  refine ⟨134314672107810564730369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179086229477080752973825 134314672107810564730369)
                  ·
                    rfl

theorem cell20_294274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_294274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294274 prefixEnd_294274 := by exact prefixLift 294274
  have htrace : WordTrace (prefixWord ++ tailWord_294274) baseStart_294274 baseEnd_294274 := by
    simpa [prefixWord, tailWord_294274, baseEnd_294274] using wordTrace_append hprefix tailTrace_294274
  have hstable : (prefixWord ++ tailWord_294274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294274).length < 2 ^ (prefixWord ++ tailWord_294274).sum := by decide
  have hdescent : baseEnd_294274 < baseStart_294274 := by decide
  rcases family_descends (prefixWord ++ tailWord_294274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294275 : List Nat := [1, 1, 1, 3, 5, 2, 2, 2, 3]
def baseStart_294275 : Nat := 118140960795 + 294275 * 2 ^ 59
def prefixEnd_294275 : Nat := 4983230072969 + 3 ^ 40 * 294275 * 2
def baseEnd_294275 : Nat := 134315128535059005697031

theorem tailTrace_294275 : CollatzResearch.WordTrace tailWord_294275 prefixEnd_294275 134315128535059005697031 := by
  unfold tailWord_294275
  simp only [CollatzResearch.WordTrace]
  refine ⟨10733091008899408013852279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7155394005932938675901519 10733091008899408013852279)
  ·
    refine ⟨16099636513349112020778419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10733091008899408013852279 16099636513349112020778419)
    ·
      refine ⟨24149454770023668031167629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16099636513349112020778419 24149454770023668031167629)
      ·
        refine ⟨9056045538758875511687861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24149454770023668031167629 9056045538758875511687861)
        ·
          refine ⟨849004269258644579220737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9056045538758875511687861 849004269258644579220737)
          ·
            refine ⟨636753201943983434415553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 849004269258644579220737 636753201943983434415553)
            ·
              refine ⟨477564901457987575811665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 636753201943983434415553 477564901457987575811665)
              ·
                refine ⟨358173676093490681858749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477564901457987575811665 358173676093490681858749)
                ·
                  refine ⟨134315128535059005697031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 358173676093490681858749 134315128535059005697031)
                  ·
                    rfl

theorem cell20_294275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 3].length) (baseStart_294275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294275 prefixEnd_294275 := by exact prefixLift 294275
  have htrace : WordTrace (prefixWord ++ tailWord_294275) baseStart_294275 baseEnd_294275 := by
    simpa [prefixWord, tailWord_294275, baseEnd_294275] using wordTrace_append hprefix tailTrace_294275
  have hstable : (prefixWord ++ tailWord_294275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294275).length < 2 ^ (prefixWord ++ tailWord_294275).sum := by decide
  have hdescent : baseEnd_294275 < baseStart_294275 := by decide
  rcases family_descends (prefixWord ++ tailWord_294275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294303 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 6]
def baseStart_294303 : Nat := 118140960795 + 294303 * 2 ^ 59
def prefixEnd_294303 : Nat := 4983230072969 + 3 ^ 40 * 294303 * 2
def baseEnd_294303 : Nat := 134327908498015352763583

theorem tailTrace_294303 : CollatzResearch.WordTrace tailWord_294303 prefixEnd_294303 134327908498015352763583 := by
  unfold tailWord_294303
  simp only [CollatzResearch.WordTrace]
  refine ⟨10734112252797968795871563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7156074835198645863914375 10734112252797968795871563)
  ·
    refine ⟨16101168379196953193807345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10734112252797968795871563 16101168379196953193807345)
    ·
      refine ⟨12075876284397714895355509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16101168379196953193807345 12075876284397714895355509)
      ·
        refine ⟨1132113401662285771439579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12075876284397714895355509 1132113401662285771439579)
        ·
          refine ⟨1698170102493428657159369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132113401662285771439579 1698170102493428657159369)
          ·
            refine ⟨1273627576870071492869527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1698170102493428657159369 1273627576870071492869527)
            ·
              refine ⟨1910441365305107239304291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1273627576870071492869527 1910441365305107239304291)
              ·
                refine ⟨2865662047957660858956437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1910441365305107239304291 2865662047957660858956437)
                ·
                  refine ⟨134327908498015352763583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2865662047957660858956437 134327908498015352763583)
                  ·
                    rfl

theorem cell20_294303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_294303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294303 prefixEnd_294303 := by exact prefixLift 294303
  have htrace : WordTrace (prefixWord ++ tailWord_294303) baseStart_294303 baseEnd_294303 := by
    simpa [prefixWord, tailWord_294303, baseEnd_294303] using wordTrace_append hprefix tailTrace_294303
  have hstable : (prefixWord ++ tailWord_294303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294303).length < 2 ^ (prefixWord ++ tailWord_294303).sum := by decide
  have hdescent : baseEnd_294303 < baseStart_294303 := by decide
  rcases family_descends (prefixWord ++ tailWord_294303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294306 : List Nat := [3, 3, 1, 2, 1, 3, 3, 4]
def baseStart_294306 : Nat := 118140960795 + 294306 * 2 ^ 59
def prefixEnd_294306 : Nat := 4983230072969 + 3 ^ 40 * 294306 * 2
def baseEnd_294306 : Nat := 44776425926586891887857

theorem tailTrace_294306 : CollatzResearch.WordTrace tailWord_294306 prefixEnd_294306 44776425926586891887857 := by
  unfold tailWord_294306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2683555417946775077057693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7156147781191400205487181 2683555417946775077057693)
  ·
    refine ⟨1006333281730040653896635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2683555417946775077057693 1006333281730040653896635)
    ·
      refine ⟨1509499922595060980844953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1006333281730040653896635 1509499922595060980844953)
      ·
        refine ⟨1132124941946295735633715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1509499922595060980844953 1132124941946295735633715)
        ·
          refine ⟨1698187412919443603450573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132124941946295735633715 1698187412919443603450573)
          ·
            refine ⟨636820279844791351293965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1698187412919443603450573 636820279844791351293965)
            ·
              refine ⟨238807604941796756735237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 636820279844791351293965 238807604941796756735237)
              ·
                refine ⟨44776425926586891887857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 238807604941796756735237 44776425926586891887857)
                ·
                  rfl

theorem cell20_294306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_294306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294306 prefixEnd_294306 := by exact prefixLift 294306
  have htrace : WordTrace (prefixWord ++ tailWord_294306) baseStart_294306 baseEnd_294306 := by
    simpa [prefixWord, tailWord_294306, baseEnd_294306] using wordTrace_append hprefix tailTrace_294306
  have hstable : (prefixWord ++ tailWord_294306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294306).length < 2 ^ (prefixWord ++ tailWord_294306).sum := by decide
  have hdescent : baseEnd_294306 < baseStart_294306 := by decide
  rcases family_descends (prefixWord ++ tailWord_294306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294365 : List Nat := [1, 4, 3, 1, 1, 3, 1, 6]
def baseStart_294365 : Nat := 118140960795 + 294365 * 2 ^ 59
def prefixEnd_294365 : Nat := 4983230072969 + 3 ^ 40 * 294365 * 2
def baseEnd_294365 : Nat := 44785402329139564232221

theorem tailTrace_294365 : CollatzResearch.WordTrace tailWord_294365 prefixEnd_294365 44785402329139564232221 := by
  unfold tailWord_294365
  simp only [CollatzResearch.WordTrace]
  refine ⟨10736373578573353384628549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7157582385715568923085699 10736373578573353384628549)
  ·
    refine ⟨2013070045982503759617853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10736373578573353384628549 2013070045982503759617853)
    ·
      refine ⟨754901267243438909856695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2013070045982503759617853 754901267243438909856695)
      ·
        refine ⟨1132351900865158364785043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 754901267243438909856695 1132351900865158364785043)
        ·
          refine ⟨1698527851297737547177565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132351900865158364785043 1698527851297737547177565)
          ·
            refine ⟨636947944236651580191587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1698527851297737547177565 636947944236651580191587)
            ·
              refine ⟨955421916354977370287381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636947944236651580191587 955421916354977370287381)
              ·
                refine ⟨44785402329139564232221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 955421916354977370287381 44785402329139564232221)
                ·
                  rfl

theorem cell20_294365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 6].length) (baseStart_294365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294365 prefixEnd_294365 := by exact prefixLift 294365
  have htrace : WordTrace (prefixWord ++ tailWord_294365) baseStart_294365 baseEnd_294365 := by
    simpa [prefixWord, tailWord_294365, baseEnd_294365] using wordTrace_append hprefix tailTrace_294365
  have hstable : (prefixWord ++ tailWord_294365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294365).length < 2 ^ (prefixWord ++ tailWord_294365).sum := by decide
  have hdescent : baseEnd_294365 < baseStart_294365 := by decide
  rcases family_descends (prefixWord ++ tailWord_294365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294375 : List Nat := [1, 1, 5, 2, 1, 2, 3, 3, 2]
def baseStart_294375 : Nat := 118140960795 + 294375 * 2 ^ 59
def prefixEnd_294375 : Nat := 4983230072969 + 3 ^ 40 * 294375 * 2
def baseEnd_294375 : Nat := 134360771259903102363289

theorem tailTrace_294375 : CollatzResearch.WordTrace tailWord_294375 prefixEnd_294375 134360771259903102363289 := by
  unfold tailWord_294375
  simp only [CollatzResearch.WordTrace]
  refine ⟨10736738308537125092492579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7157825539024750061661719 10736738308537125092492579)
  ·
    refine ⟨16105107462805687638738869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10736738308537125092492579 16105107462805687638738869)
    ·
      refine ⟨1509853824638033216131769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16105107462805687638738869 1509853824638033216131769)
      ·
        refine ⟨1132390368478524912098827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1509853824638033216131769 1132390368478524912098827)
        ·
          refine ⟨1698585552717787368148241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1132390368478524912098827 1698585552717787368148241)
          ·
            refine ⟨1273939164538340526111181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1698585552717787368148241 1273939164538340526111181)
            ·
              refine ⟨477727186701877697291693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1273939164538340526111181 477727186701877697291693)
              ·
                refine ⟨179147695013204136484385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 477727186701877697291693 179147695013204136484385)
                ·
                  refine ⟨134360771259903102363289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179147695013204136484385 134360771259903102363289)
                  ·
                    rfl

theorem cell20_294375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 2].length) (baseStart_294375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294375 prefixEnd_294375 := by exact prefixLift 294375
  have htrace : WordTrace (prefixWord ++ tailWord_294375) baseStart_294375 baseEnd_294375 := by
    simpa [prefixWord, tailWord_294375, baseEnd_294375] using wordTrace_append hprefix tailTrace_294375
  have hstable : (prefixWord ++ tailWord_294375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294375).length < 2 ^ (prefixWord ++ tailWord_294375).sum := by decide
  have hdescent : baseEnd_294375 < baseStart_294375 := by decide
  rcases family_descends (prefixWord ++ tailWord_294375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294389 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 5]
def baseStart_294389 : Nat := 118140960795 + 294389 * 2 ^ 59
def prefixEnd_294389 : Nat := 4983230072969 + 3 ^ 40 * 294389 * 2
def baseEnd_294389 : Nat := 134367161241381275896565

theorem tailTrace_294389 : CollatzResearch.WordTrace tailWord_294389 prefixEnd_294389 134367161241381275896565 := by
  unfold tailWord_294389
  simp only [CollatzResearch.WordTrace]
  refine ⟨10737248930486405483502221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7158165953657603655668147 10737248930486405483502221)
  ·
    refine ⟨4026468348932402056313333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10737248930486405483502221 4026468348932402056313333)
    ·
      refine ⟨377481407712412692779375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4026468348932402056313333 377481407712412692779375)
      ·
        refine ⟨566222111568619039169063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377481407712412692779375 566222111568619039169063)
        ·
          refine ⟨849333167352928558753595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566222111568619039169063 849333167352928558753595)
          ·
            refine ⟨1273999751029392838130393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 849333167352928558753595 1273999751029392838130393)
            ·
              refine ⟨955499813272044628597795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1273999751029392838130393 955499813272044628597795)
              ·
                refine ⟨1433249719908066942896693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955499813272044628597795 1433249719908066942896693)
                ·
                  refine ⟨134367161241381275896565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1433249719908066942896693 134367161241381275896565)
                  ·
                    rfl

theorem cell20_294389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_294389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294389 prefixEnd_294389 := by exact prefixLift 294389
  have htrace : WordTrace (prefixWord ++ tailWord_294389) baseStart_294389 baseEnd_294389 := by
    simpa [prefixWord, tailWord_294389, baseEnd_294389] using wordTrace_append hprefix tailTrace_294389
  have hstable : (prefixWord ++ tailWord_294389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294389).length < 2 ^ (prefixWord ++ tailWord_294389).sum := by decide
  have hdescent : baseEnd_294389 < baseStart_294389 := by decide
  rcases family_descends (prefixWord ++ tailWord_294389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294396 : List Nat := [2, 2, 2, 1, 2, 1, 2, 6, 2]
def baseStart_294396 : Nat := 118140960795 + 294396 * 2 ^ 59
def prefixEnd_294396 : Nat := 4983230072969 + 3 ^ 40 * 294396 * 2
def baseEnd_294396 : Nat := 134370356232120362663203

theorem tailTrace_294396 : CollatzResearch.WordTrace tailWord_294396 prefixEnd_294396 134370356232120362663203 := by
  unfold tailWord_294396
  simp only [CollatzResearch.WordTrace]
  refine ⟨5368752120730522839503521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7158336160974030452671361 5368752120730522839503521)
  ·
    refine ⟨4026564090547892129627641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5368752120730522839503521 4026564090547892129627641)
    ·
      refine ⟨3019923067910919097220731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4026564090547892129627641 3019923067910919097220731)
      ·
        refine ⟨4529884601866378645831097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3019923067910919097220731 4529884601866378645831097)
        ·
          refine ⟨3397413451399783984373323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4529884601866378645831097 3397413451399783984373323)
          ·
            refine ⟨5096120177099675976559985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3397413451399783984373323 5096120177099675976559985)
            ·
              refine ⟨3822090132824756982419989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5096120177099675976559985 3822090132824756982419989)
              ·
                refine ⟨179160474976160483550937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3822090132824756982419989 179160474976160483550937)
                ·
                  refine ⟨134370356232120362663203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179160474976160483550937 134370356232120362663203)
                  ·
                    rfl

theorem cell20_294396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 6, 2].length) (baseStart_294396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294396 prefixEnd_294396 := by exact prefixLift 294396
  have htrace : WordTrace (prefixWord ++ tailWord_294396) baseStart_294396 baseEnd_294396 := by
    simpa [prefixWord, tailWord_294396, baseEnd_294396] using wordTrace_append hprefix tailTrace_294396
  have hstable : (prefixWord ++ tailWord_294396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294396).length < 2 ^ (prefixWord ++ tailWord_294396).sum := by decide
  have hdescent : baseEnd_294396 < baseStart_294396 := by decide
  rcases family_descends (prefixWord ++ tailWord_294396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294431 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 7]
def baseStart_294431 : Nat := 118140960795 + 294431 * 2 ^ 59
def prefixEnd_294431 : Nat := 4983230072969 + 3 ^ 40 * 294431 * 2
def baseEnd_294431 : Nat := 134386331185815796496393

theorem tailTrace_294431 : CollatzResearch.WordTrace tailWord_294431 prefixEnd_294431 134386331185815796496393 := by
  unfold tailWord_294431
  simp only [CollatzResearch.WordTrace]
  refine ⟨10738780796334246656531147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7159187197556164437687431 10738780796334246656531147)
  ·
    refine ⟨16108171194501369984796721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10738780796334246656531147 16108171194501369984796721)
    ·
      refine ⟨12081128395876027488597541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16108171194501369984796721 12081128395876027488597541)
      ·
        refine ⟨2265211574226755154112039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12081128395876027488597541 2265211574226755154112039)
        ·
          refine ⟨3397817361340132731168059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2265211574226755154112039 3397817361340132731168059)
          ·
            refine ⟨5096726042010199096752089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3397817361340132731168059 5096726042010199096752089)
            ·
              refine ⟨3822544531507649322564067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5096726042010199096752089 3822544531507649322564067)
              ·
                refine ⟨5733816797261473983846101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3822544531507649322564067 5733816797261473983846101)
                ·
                  refine ⟨134386331185815796496393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5733816797261473983846101 134386331185815796496393)
                  ·
                    rfl

theorem cell20_294431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_294431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294431 prefixEnd_294431 := by exact prefixLift 294431
  have htrace : WordTrace (prefixWord ++ tailWord_294431) baseStart_294431 baseEnd_294431 := by
    simpa [prefixWord, tailWord_294431, baseEnd_294431] using wordTrace_append hprefix tailTrace_294431
  have hstable : (prefixWord ++ tailWord_294431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294431).length < 2 ^ (prefixWord ++ tailWord_294431).sum := by decide
  have hdescent : baseEnd_294431 < baseStart_294431 := by decide
  rcases family_descends (prefixWord ++ tailWord_294431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294451 : List Nat := [1, 1, 1, 2, 4, 3, 4, 2, 2]
def baseStart_294451 : Nat := 118140960795 + 294451 * 2 ^ 59
def prefixEnd_294451 : Nat := 4983230072969 + 3 ^ 40 * 294451 * 2
def baseEnd_294451 : Nat := 134395459730784615829645

theorem tailTrace_294451 : CollatzResearch.WordTrace tailWord_294451 prefixEnd_294451 134395459730784615829645 := by
  unfold tailWord_294451
  simp only [CollatzResearch.WordTrace]
  refine ⟨10739510256261790072259207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7159673504174526714839471 10739510256261790072259207)
  ·
    refine ⟨16109265384392685108388811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10739510256261790072259207 16109265384392685108388811)
    ·
      refine ⟨24163898076589027662583217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16109265384392685108388811 24163898076589027662583217)
      ·
        refine ⟨18122923557441770746937413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24163898076589027662583217 18122923557441770746937413)
        ·
          refine ⟨3398048167020332015050765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18122923557441770746937413 3398048167020332015050765)
          ·
            refine ⟨1274268062632624505644037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3398048167020332015050765 1274268062632624505644037)
            ·
              refine ⟨238925261743617094808257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1274268062632624505644037 238925261743617094808257)
              ·
                refine ⟨179193946307712821106193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238925261743617094808257 179193946307712821106193)
                ·
                  refine ⟨134395459730784615829645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179193946307712821106193 134395459730784615829645)
                  ·
                    rfl

theorem cell20_294451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 2].length) (baseStart_294451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294451 prefixEnd_294451 := by exact prefixLift 294451
  have htrace : WordTrace (prefixWord ++ tailWord_294451) baseStart_294451 baseEnd_294451 := by
    simpa [prefixWord, tailWord_294451, baseEnd_294451] using wordTrace_append hprefix tailTrace_294451
  have hstable : (prefixWord ++ tailWord_294451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294451).length < 2 ^ (prefixWord ++ tailWord_294451).sum := by decide
  have hdescent : baseEnd_294451 < baseStart_294451 := by decide
  rcases family_descends (prefixWord ++ tailWord_294451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294500 : List Nat := [2, 3, 1, 1, 2, 4, 7]
def baseStart_294500 : Nat := 118140960795 + 294500 * 2 ^ 59
def prefixEnd_294500 : Nat := 4983230072969 + 3 ^ 40 * 294500 * 2
def baseEnd_294500 : Nat := 14935313851773135910679

theorem tailTrace_294500 : CollatzResearch.WordTrace tailWord_294500 prefixEnd_294500 14935313851773135910679 := by
  unfold tailWord_294500
  simp only [CollatzResearch.WordTrace]
  refine ⟨5370648716542135720396477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7160864955389514293861969 5370648716542135720396477)
  ·
    refine ⟨2013993268703300895148679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5370648716542135720396477 2013993268703300895148679)
    ·
      refine ⟨3020989903054951342723019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2013993268703300895148679 3020989903054951342723019)
      ·
        refine ⟨4531484854582427014084529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3020989903054951342723019 4531484854582427014084529)
        ·
          refine ⟨3398613640936820260563397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4531484854582427014084529 3398613640936820260563397)
          ·
            refine ⟨637240057675653798855637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3398613640936820260563397 637240057675653798855637)
            ·
              refine ⟨14935313851773135910679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 637240057675653798855637 14935313851773135910679)
              ·
                rfl

theorem cell20_294500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 7].length) (baseStart_294500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294500 prefixEnd_294500 := by exact prefixLift 294500
  have htrace : WordTrace (prefixWord ++ tailWord_294500) baseStart_294500 baseEnd_294500 := by
    simpa [prefixWord, tailWord_294500, baseEnd_294500] using wordTrace_append hprefix tailTrace_294500
  have hstable : (prefixWord ++ tailWord_294500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294500).length < 2 ^ (prefixWord ++ tailWord_294500).sum := by decide
  have hdescent : baseEnd_294500 < baseStart_294500 := by decide
  rcases family_descends (prefixWord ++ tailWord_294500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294620 : List Nat := [2, 2, 5, 1, 2, 1, 1, 4, 2]
def baseStart_294620 : Nat := 118140960795 + 294620 * 2 ^ 59
def prefixEnd_294620 : Nat := 4983230072969 + 3 ^ 40 * 294620 * 2
def baseEnd_294620 : Nat := 134472595935771139195621

theorem tailTrace_294620 : CollatzResearch.WordTrace tailWord_294620 prefixEnd_294620 134472595935771139195621 := by
  unfold tailWord_294620
  simp only [CollatzResearch.WordTrace]
  refine ⟨5372837096324765967580657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7163782795099687956774209 5372837096324765967580657)
  ·
    refine ⟨4029627822243574475685493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5372837096324765967580657 4029627822243574475685493)
    ·
      refine ⟨377777608335335107095515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4029627822243574475685493 377777608335335107095515)
      ·
        refine ⟨566666412503002660643273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377777608335335107095515 566666412503002660643273)
        ·
          refine ⟨424999809377251995482455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 566666412503002660643273 424999809377251995482455)
          ·
            refine ⟨637499714065877993223683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424999809377251995482455 637499714065877993223683)
            ·
              refine ⟨956249571098816989835525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637499714065877993223683 956249571098816989835525)
              ·
                refine ⟨179296794581028185594161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 956249571098816989835525 179296794581028185594161)
                ·
                  refine ⟨134472595935771139195621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179296794581028185594161 134472595935771139195621)
                  ·
                    rfl

theorem cell20_294620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_294620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294620 prefixEnd_294620 := by exact prefixLift 294620
  have htrace : WordTrace (prefixWord ++ tailWord_294620) baseStart_294620 baseEnd_294620 := by
    simpa [prefixWord, tailWord_294620, baseEnd_294620] using wordTrace_append hprefix tailTrace_294620
  have hstable : (prefixWord ++ tailWord_294620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294620).length < 2 ^ (prefixWord ++ tailWord_294620).sum := by decide
  have hdescent : baseEnd_294620 < baseStart_294620 := by decide
  rcases family_descends (prefixWord ++ tailWord_294620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294638 : List Nat := [4, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_294638 : Nat := 118140960795 + 294638 * 2 ^ 59
def prefixEnd_294638 : Nat := 4983230072969 + 3 ^ 40 * 294638 * 2
def baseEnd_294638 : Nat := 134480811626243076595547

theorem tailTrace_294638 : CollatzResearch.WordTrace tailWord_294638 prefixEnd_294638 134480811626243076595547 := by
  unfold tailWord_294638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1343291338323040126164571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7164220471056214006211045 1343291338323040126164571)
  ·
    refine ⟨2014937007484560189246857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1343291338323040126164571 2014937007484560189246857)
    ·
      refine ⟨1511202755613420141935143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2014937007484560189246857 1511202755613420141935143)
      ·
        refine ⟨2266804133420130212902715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511202755613420141935143 2266804133420130212902715)
        ·
          refine ⟨3400206200130195319354073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266804133420130212902715 3400206200130195319354073)
          ·
            refine ⟨2550154650097646489515555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3400206200130195319354073 2550154650097646489515555)
            ·
              refine ⟨3825231975146469734273333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2550154650097646489515555 3825231975146469734273333)
              ·
                refine ⟨358615497669981537588125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3825231975146469734273333 358615497669981537588125)
                ·
                  refine ⟨134480811626243076595547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 358615497669981537588125 134480811626243076595547)
                  ·
                    rfl

theorem cell20_294638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_294638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294638 prefixEnd_294638 := by exact prefixLift 294638
  have htrace : WordTrace (prefixWord ++ tailWord_294638) baseStart_294638 baseEnd_294638 := by
    simpa [prefixWord, tailWord_294638, baseEnd_294638] using wordTrace_append hprefix tailTrace_294638
  have hstable : (prefixWord ++ tailWord_294638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294638).length < 2 ^ (prefixWord ++ tailWord_294638).sum := by decide
  have hdescent : baseEnd_294638 < baseStart_294638 := by decide
  rcases family_descends (prefixWord ++ tailWord_294638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294690 : List Nat := [3, 3, 1, 1, 2, 1, 2, 7]
def baseStart_294690 : Nat := 118140960795 + 294690 * 2 ^ 59
def prefixEnd_294690 : Nat := 4983230072969 + 3 ^ 40 * 294690 * 2
def baseEnd_294690 : Nat := 44834848614387335620667

theorem tailTrace_294690 : CollatzResearch.WordTrace tailWord_294690 prefixEnd_294690 44834848614387335620667 := by
  unfold tailWord_294690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2687056825598983472552381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7165484868263955926806349 2687056825598983472552381)
  ·
    refine ⟨1007646309599618802207143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2687056825598983472552381 1007646309599618802207143)
    ·
      refine ⟨1511469464399428203310715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1007646309599618802207143 1511469464399428203310715)
      ·
        refine ⟨2267204196599142304966073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511469464399428203310715 2267204196599142304966073)
        ·
          refine ⟨1700403147449356728724555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2267204196599142304966073 1700403147449356728724555)
          ·
            refine ⟨2550604721174035093086833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1700403147449356728724555 2550604721174035093086833)
            ·
              refine ⟨1912953540880526319815125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2550604721174035093086833 1912953540880526319815125)
              ·
                refine ⟨44834848614387335620667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1912953540880526319815125 44834848614387335620667)
                ·
                  rfl

theorem cell20_294690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_294690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294690 prefixEnd_294690 := by exact prefixLift 294690
  have htrace : WordTrace (prefixWord ++ tailWord_294690) baseStart_294690 baseEnd_294690 := by
    simpa [prefixWord, tailWord_294690, baseEnd_294690] using wordTrace_append hprefix tailTrace_294690
  have hstable : (prefixWord ++ tailWord_294690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294690).length < 2 ^ (prefixWord ++ tailWord_294690).sum := by decide
  have hdescent : baseEnd_294690 < baseStart_294690 := by decide
  rcases family_descends (prefixWord ++ tailWord_294690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294693 : List Nat := [1, 3, 1, 2, 3, 3, 3, 1, 3]
def baseStart_294693 : Nat := 118140960795 + 294693 * 2 ^ 59
def prefixEnd_294693 : Nat := 4983230072969 + 3 ^ 40 * 294693 * 2
def baseEnd_294693 : Nat := 134505915124907329761989

theorem tailTrace_294693 : CollatzResearch.WordTrace tailWord_294693 prefixEnd_294693 134505915124907329761989 := by
  unfold tailWord_294693
  simp only [CollatzResearch.WordTrace]
  refine ⟨10748336721385065402568733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7165557814256710268379155 10748336721385065402568733)
  ·
    refine ⟨4030626270519399525963275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10748336721385065402568733 4030626270519399525963275)
    ·
      refine ⟨6045939405779099288944913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4030626270519399525963275 6045939405779099288944913)
      ·
        refine ⟨4534454554334324466708685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6045939405779099288944913 4534454554334324466708685)
        ·
          refine ⟨1700420457875371675015757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4534454554334324466708685 1700420457875371675015757)
          ·
            refine ⟨637657671703264378130909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1700420457875371675015757 637657671703264378130909)
            ·
              refine ⟨239121626888724141799091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 637657671703264378130909 239121626888724141799091)
              ·
                refine ⟨358682440333086212698637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239121626888724141799091 358682440333086212698637)
                ·
                  refine ⟨134505915124907329761989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 358682440333086212698637 134505915124907329761989)
                  ·
                    rfl

theorem cell20_294693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_294693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294693 prefixEnd_294693 := by exact prefixLift 294693
  have htrace : WordTrace (prefixWord ++ tailWord_294693) baseStart_294693 baseEnd_294693 := by
    simpa [prefixWord, tailWord_294693, baseEnd_294693] using wordTrace_append hprefix tailTrace_294693
  have hstable : (prefixWord ++ tailWord_294693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294693).length < 2 ^ (prefixWord ++ tailWord_294693).sum := by decide
  have hdescent : baseEnd_294693 < baseStart_294693 := by decide
  rcases family_descends (prefixWord ++ tailWord_294693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294713 : List Nat := [1, 2, 1, 7, 2, 1, 1, 3, 2]
def baseStart_294713 : Nat := 118140960795 + 294713 * 2 ^ 59
def prefixEnd_294713 : Nat := 4983230072969 + 3 ^ 40 * 294713 * 2
def baseEnd_294713 : Nat := 134515043669876149095241

theorem tailTrace_294713 : CollatzResearch.WordTrace tailWord_294713 prefixEnd_294713 134515043669876149095241 := by
  unfold tailWord_294713
  simp only [CollatzResearch.WordTrace]
  refine ⟨10749066181312608818296793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7166044120875072545531195 10749066181312608818296793)
  ·
    refine ⟨8061799635984456613722595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10749066181312608818296793 8061799635984456613722595)
    ·
      refine ⟨12092699453976684920583893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8061799635984456613722595 12092699453976684920583893)
      ·
        refine ⟨283422643452578552826185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 12092699453976684920583893 283422643452578552826185)
        ·
          refine ⟨212566982589433914619639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283422643452578552826185 212566982589433914619639)
          ·
            refine ⟨318850473884150871929459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212566982589433914619639 318850473884150871929459)
            ·
              refine ⟨478275710826226307894189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318850473884150871929459 478275710826226307894189)
              ·
                refine ⟨179353391559834865460321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 478275710826226307894189 179353391559834865460321)
                ·
                  refine ⟨134515043669876149095241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179353391559834865460321 134515043669876149095241)
                  ·
                    rfl

theorem cell20_294713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 2].length) (baseStart_294713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294713 prefixEnd_294713 := by exact prefixLift 294713
  have htrace : WordTrace (prefixWord ++ tailWord_294713) baseStart_294713 baseEnd_294713 := by
    simpa [prefixWord, tailWord_294713, baseEnd_294713] using wordTrace_append hprefix tailTrace_294713
  have hstable : (prefixWord ++ tailWord_294713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294713).length < 2 ^ (prefixWord ++ tailWord_294713).sum := by decide
  have hdescent : baseEnd_294713 < baseStart_294713 := by decide
  rcases family_descends (prefixWord ++ tailWord_294713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294717 : List Nat := [1, 4, 1, 4, 1, 1, 3, 3, 2]
def baseStart_294717 : Nat := 118140960795 + 294717 * 2 ^ 59
def prefixEnd_294717 : Nat := 4983230072969 + 3 ^ 40 * 294717 * 2
def baseEnd_294717 : Nat := 134516869378869912961891

theorem tailTrace_294717 : CollatzResearch.WordTrace tailWord_294717 prefixEnd_294717 134516869378869912961891 := by
  unfold tailWord_294717
  simp only [CollatzResearch.WordTrace]
  refine ⟨10749212073298117501442405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7166141382198745000961603 10749212073298117501442405)
  ·
    refine ⟨2015477263743397031520451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10749212073298117501442405 2015477263743397031520451)
    ·
      refine ⟨3023215895615095547280677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2015477263743397031520451 3023215895615095547280677)
      ·
        refine ⟨566852980427830415115127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3023215895615095547280677 566852980427830415115127)
        ·
          refine ⟨850279470641745622672691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566852980427830415115127 850279470641745622672691)
          ·
            refine ⟨1275419205962618434009037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850279470641745622672691 1275419205962618434009037)
            ·
              refine ⟨478282202235981912753389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1275419205962618434009037 478282202235981912753389)
              ·
                refine ⟨179355825838493217282521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 478282202235981912753389 179355825838493217282521)
                ·
                  refine ⟨134516869378869912961891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179355825838493217282521 134516869378869912961891)
                  ·
                    rfl

theorem cell20_294717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_294717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294717 prefixEnd_294717 := by exact prefixLift 294717
  have htrace : WordTrace (prefixWord ++ tailWord_294717) baseStart_294717 baseEnd_294717 := by
    simpa [prefixWord, tailWord_294717, baseEnd_294717] using wordTrace_append hprefix tailTrace_294717
  have hstable : (prefixWord ++ tailWord_294717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294717).length < 2 ^ (prefixWord ++ tailWord_294717).sum := by decide
  have hdescent : baseEnd_294717 < baseStart_294717 := by decide
  rcases family_descends (prefixWord ++ tailWord_294717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294728 : List Nat := [2, 1, 3, 1, 1, 6, 6]
def baseStart_294728 : Nat := 118140960795 + 294728 * 2 ^ 59
def prefixEnd_294728 : Nat := 4983230072969 + 3 ^ 40 * 294728 * 2
def baseEnd_294728 : Nat := 14946876675400307066131

theorem tailTrace_294728 : CollatzResearch.WordTrace tailWord_294728 prefixEnd_294728 14946876675400307066131 := by
  unfold tailWord_294728
  simp only [CollatzResearch.WordTrace]
  refine ⟨5374806638129133190046419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7166408850838844253395225 5374806638129133190046419)
  ·
    refine ⟨8062209957193699785069629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5374806638129133190046419 8062209957193699785069629)
    ·
      refine ⟨3023328733947637419401111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8062209957193699785069629 3023328733947637419401111)
      ·
        refine ⟨4534993100921456129101667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3023328733947637419401111 4534993100921456129101667)
        ·
          refine ⟨6802489651382184193652501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4534993100921456129101667 6802489651382184193652501)
          ·
            refine ⟨318866702408539884077461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6802489651382184193652501 318866702408539884077461)
            ·
              refine ⟨14946876675400307066131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 318866702408539884077461 14946876675400307066131)
              ·
                rfl

theorem cell20_294728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 6].length) (baseStart_294728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294728 prefixEnd_294728 := by exact prefixLift 294728
  have htrace : WordTrace (prefixWord ++ tailWord_294728) baseStart_294728 baseEnd_294728 := by
    simpa [prefixWord, tailWord_294728, baseEnd_294728] using wordTrace_append hprefix tailTrace_294728
  have hstable : (prefixWord ++ tailWord_294728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294728).length < 2 ^ (prefixWord ++ tailWord_294728).sum := by decide
  have hdescent : baseEnd_294728 < baseStart_294728 := by decide
  rcases family_descends (prefixWord ++ tailWord_294728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294738 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 4]
def baseStart_294738 : Nat := 118140960795 + 294738 * 2 ^ 59
def prefixEnd_294738 : Nat := 4983230072969 + 3 ^ 40 * 294738 * 2
def baseEnd_294738 : Nat := 134526454351087173261805

theorem tailTrace_294738 : CollatzResearch.WordTrace tailWord_294738 prefixEnd_294738 134526454351087173261805 := by
  unfold tailWord_294738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2687494501555509521989217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7166652004148025391971245 2687494501555509521989217)
  ·
    refine ⟨2015620876166632141491913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2687494501555509521989217 2015620876166632141491913)
    ·
      refine ⟨1511715657124974106118935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2015620876166632141491913 1511715657124974106118935)
      ·
        refine ⟨2267573485687461159178403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511715657124974106118935 2267573485687461159178403)
        ·
          refine ⟨3401360228531191738767605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267573485687461159178403 3401360228531191738767605)
          ·
            refine ⟨318877521424799225509463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3401360228531191738767605 318877521424799225509463)
            ·
              refine ⟨478316282137198838264195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318877521424799225509463 478316282137198838264195)
              ·
                refine ⟨717474423205798257396293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 478316282137198838264195 717474423205798257396293)
                ·
                  refine ⟨134526454351087173261805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 717474423205798257396293 134526454351087173261805)
                  ·
                    rfl

theorem cell20_294738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_294738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294738 prefixEnd_294738 := by exact prefixLift 294738
  have htrace : WordTrace (prefixWord ++ tailWord_294738) baseStart_294738 baseEnd_294738 := by
    simpa [prefixWord, tailWord_294738, baseEnd_294738] using wordTrace_append hprefix tailTrace_294738
  have hstable : (prefixWord ++ tailWord_294738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294738).length < 2 ^ (prefixWord ++ tailWord_294738).sum := by decide
  have hdescent : baseEnd_294738 < baseStart_294738 := by decide
  rcases family_descends (prefixWord ++ tailWord_294738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294752 : List Nat := [2, 1, 1, 3, 3, 3, 1, 3, 3]
def baseStart_294752 : Nat := 118140960795 + 294752 * 2 ^ 59
def prefixEnd_294752 : Nat := 4983230072969 + 3 ^ 40 * 294752 * 2
def baseEnd_294752 : Nat := 134532844332565346795081

theorem tailTrace_294752 : CollatzResearch.WordTrace tailWord_294752 prefixEnd_294752 134532844332565346795081 := by
  unfold tailWord_294752
  simp only [CollatzResearch.WordTrace]
  refine ⟨5375244314085659239483255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7166992418780878985977673 5375244314085659239483255)
  ·
    refine ⟨8062866471128488859224883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5375244314085659239483255 8062866471128488859224883)
    ·
      refine ⟨12094299706692733288837325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8062866471128488859224883 12094299706692733288837325)
      ·
        refine ⟨4535362390009774983313997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12094299706692733288837325 4535362390009774983313997)
        ·
          refine ⟨1700760896253665618742749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4535362390009774983313997 1700760896253665618742749)
          ·
            refine ⟨637785336095124607028531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1700760896253665618742749 637785336095124607028531)
            ·
              refine ⟨956678004142686910542797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637785336095124607028531 956678004142686910542797)
              ·
                refine ⟨358754251553507591453549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 956678004142686910542797 358754251553507591453549)
                ·
                  refine ⟨134532844332565346795081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 358754251553507591453549 134532844332565346795081)
                  ·
                    rfl

theorem cell20_294752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 3].length) (baseStart_294752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294752 prefixEnd_294752 := by exact prefixLift 294752
  have htrace : WordTrace (prefixWord ++ tailWord_294752) baseStart_294752 baseEnd_294752 := by
    simpa [prefixWord, tailWord_294752, baseEnd_294752] using wordTrace_append hprefix tailTrace_294752
  have hstable : (prefixWord ++ tailWord_294752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294752).length < 2 ^ (prefixWord ++ tailWord_294752).sum := by decide
  have hdescent : baseEnd_294752 < baseStart_294752 := by decide
  rcases family_descends (prefixWord ++ tailWord_294752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294787 : List Nat := [1, 1, 1, 3, 4, 10]
def baseStart_294787 : Nat := 118140960795 + 294787 * 2 ^ 59
def prefixEnd_294787 : Nat := 4983230072969 + 3 ^ 40 * 294787 * 2
def baseEnd_294787 : Nat := 4983289603194843726973

theorem tailTrace_294787 : CollatzResearch.WordTrace tailWord_294787 prefixEnd_294787 4983289603194843726973 := by
  unfold tailWord_294787
  simp only [CollatzResearch.WordTrace]
  refine ⟨10751765183044519456490615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7167843455363012970993743 10751765183044519456490615)
  ·
    refine ⟨16127647774566779184735923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10751765183044519456490615 16127647774566779184735923)
    ·
      refine ⟨24191471661850168777103885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16127647774566779184735923 24191471661850168777103885)
      ·
        refine ⟨9071801873193813291413957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24191471661850168777103885 9071801873193813291413957)
        ·
          refine ⟨1700962851223839992140117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9071801873193813291413957 1700962851223839992140117)
          ·
            refine ⟨4983289603194843726973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1700962851223839992140117 4983289603194843726973)
            ·
              rfl

theorem cell20_294787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 10].length) (baseStart_294787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294787 prefixEnd_294787 := by exact prefixLift 294787
  have htrace : WordTrace (prefixWord ++ tailWord_294787) baseStart_294787 baseEnd_294787 := by
    simpa [prefixWord, tailWord_294787, baseEnd_294787] using wordTrace_append hprefix tailTrace_294787
  have hstable : (prefixWord ++ tailWord_294787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294787).length < 2 ^ (prefixWord ++ tailWord_294787).sum := by decide
  have hdescent : baseEnd_294787 < baseStart_294787 := by decide
  rcases family_descends (prefixWord ++ tailWord_294787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294845 : List Nat := [1, 4, 1, 2, 3, 3, 1, 2, 3]
def baseStart_294845 : Nat := 118140960795 + 294845 * 2 ^ 59
def prefixEnd_294845 : Nat := 4983230072969 + 3 ^ 40 * 294845 * 2
def baseEnd_294845 : Nat := 134575292066670356694701

theorem tailTrace_294845 : CollatzResearch.WordTrace tailWord_294845 prefixEnd_294845 134575292066670356694701 := by
  unfold tailWord_294845
  simp only [CollatzResearch.WordTrace]
  refine ⟨10753880616834395362101989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7169253744556263574734659 10753880616834395362101989)
  ·
    refine ⟨2016352615656449130394123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10753880616834395362101989 2016352615656449130394123)
    ·
      refine ⟨3024528923484673695591185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2016352615656449130394123 3024528923484673695591185)
      ·
        refine ⟨2268396692613505271693389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3024528923484673695591185 2268396692613505271693389)
        ·
          refine ⟨850648759730064476885021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2268396692613505271693389 850648759730064476885021)
          ·
            refine ⟨318993284898774178831883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 850648759730064476885021 318993284898774178831883)
            ·
              refine ⟨478489927348161268247825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318993284898774178831883 478489927348161268247825)
              ·
                refine ⟨358867445511120951185869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 478489927348161268247825 358867445511120951185869)
                ·
                  refine ⟨134575292066670356694701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 358867445511120951185869 134575292066670356694701)
                  ·
                    rfl

theorem cell20_294845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_294845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294845 prefixEnd_294845 := by exact prefixLift 294845
  have htrace : WordTrace (prefixWord ++ tailWord_294845) baseStart_294845 baseEnd_294845 := by
    simpa [prefixWord, tailWord_294845, baseEnd_294845] using wordTrace_append hprefix tailTrace_294845
  have hstable : (prefixWord ++ tailWord_294845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294845).length < 2 ^ (prefixWord ++ tailWord_294845).sum := by decide
  have hdescent : baseEnd_294845 < baseStart_294845 := by decide
  rcases family_descends (prefixWord ++ tailWord_294845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294863 : List Nat := [1, 1, 2, 1, 1, 5, 2, 7]
def baseStart_294863 : Nat := 118140960795 + 294863 * 2 ^ 59
def prefixEnd_294863 : Nat := 4983230072969 + 3 ^ 40 * 294863 * 2
def baseEnd_294863 : Nat := 44861169252380764698209

theorem tailTrace_294863 : CollatzResearch.WordTrace tailWord_294863 prefixEnd_294863 44861169252380764698209 := by
  unfold tailWord_294863
  simp only [CollatzResearch.WordTrace]
  refine ⟨10754537130769184436257243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7169691420512789624171495 10754537130769184436257243)
  ·
    refine ⟨16131805696153776654385865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10754537130769184436257243 16131805696153776654385865)
    ·
      refine ⟨12098854272115332490789399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16131805696153776654385865 12098854272115332490789399)
      ·
        refine ⟨18148281408172998736184099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12098854272115332490789399 18148281408172998736184099)
        ·
          refine ⟨27222422112259498104276149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18148281408172998736184099 27222422112259498104276149)
          ·
            refine ⟨2552102073024327947275889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27222422112259498104276149 2552102073024327947275889)
            ·
              refine ⟨1914076554768245960456917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2552102073024327947275889 1914076554768245960456917)
              ·
                refine ⟨44861169252380764698209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1914076554768245960456917 44861169252380764698209)
                ·
                  rfl

theorem cell20_294863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 7].length) (baseStart_294863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294863 prefixEnd_294863 := by exact prefixLift 294863
  have htrace : WordTrace (prefixWord ++ tailWord_294863) baseStart_294863 baseEnd_294863 := by
    simpa [prefixWord, tailWord_294863, baseEnd_294863] using wordTrace_append hprefix tailTrace_294863
  have hstable : (prefixWord ++ tailWord_294863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294863).length < 2 ^ (prefixWord ++ tailWord_294863).sum := by decide
  have hdescent : baseEnd_294863 < baseStart_294863 := by decide
  rcases family_descends (prefixWord ++ tailWord_294863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294897 : List Nat := [1, 2, 2, 2, 6, 1, 6]
def baseStart_294897 : Nat := 118140960795 + 294897 * 2 ^ 59
def prefixEnd_294897 : Nat := 4983230072969 + 3 ^ 40 * 294897 * 2
def baseEnd_294897 : Nat := 14955447364843254106795

theorem tailTrace_294897 : CollatzResearch.WordTrace tailWord_294897 prefixEnd_294897 14955447364843254106795 := by
  unfold tailWord_294897
  simp only [CollatzResearch.WordTrace]
  refine ⟨10755777212646008242994945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7170518141764005495329963 10755777212646008242994945)
  ·
    refine ⟨8066832909484506182246209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10755777212646008242994945 8066832909484506182246209)
    ·
      refine ⟨6050124682113379636684657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8066832909484506182246209 6050124682113379636684657)
      ·
        refine ⟨4537593511585034727513493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6050124682113379636684657 4537593511585034727513493)
        ·
          refine ⟨212699695855548502852195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4537593511585034727513493 212699695855548502852195)
          ·
            refine ⟨319049543783322754278293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212699695855548502852195 319049543783322754278293)
            ·
              refine ⟨14955447364843254106795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 319049543783322754278293 14955447364843254106795)
              ·
                rfl

theorem cell20_294897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 6].length) (baseStart_294897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294897 prefixEnd_294897 := by exact prefixLift 294897
  have htrace : WordTrace (prefixWord ++ tailWord_294897) baseStart_294897 baseEnd_294897 := by
    simpa [prefixWord, tailWord_294897, baseEnd_294897] using wordTrace_append hprefix tailTrace_294897
  have hstable : (prefixWord ++ tailWord_294897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294897).length < 2 ^ (prefixWord ++ tailWord_294897).sum := by decide
  have hdescent : baseEnd_294897 < baseStart_294897 := by decide
  rcases family_descends (prefixWord ++ tailWord_294897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294911 : List Nat := [1, 1, 2, 2, 1, 2, 1, 8, 2]
def baseStart_294911 : Nat := 118140960795 + 294911 * 2 ^ 59
def prefixEnd_294911 : Nat := 4983230072969 + 3 ^ 40 * 294911 * 2
def baseEnd_294911 : Nat := 134605416265067460494431

theorem tailTrace_294911 : CollatzResearch.WordTrace tailWord_294911 prefixEnd_294911 134605416265067460494431 := by
  unfold tailWord_294911
  simp only [CollatzResearch.WordTrace]
  refine ⟨10756287834595288634004587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7170858556396859089336391 10756287834595288634004587)
  ·
    refine ⟨16134431751892932951006881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10756287834595288634004587 16134431751892932951006881)
    ·
      refine ⟨12100823813919699713255161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16134431751892932951006881 12100823813919699713255161)
      ·
        refine ⟨9075617860439774784941371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12100823813919699713255161 9075617860439774784941371)
        ·
          refine ⟨13613426790659662177412057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9075617860439774784941371 13613426790659662177412057)
          ·
            refine ⟨10210070092994746633059043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13613426790659662177412057 10210070092994746633059043)
            ·
              refine ⟨15315105139492119949588565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10210070092994746633059043 15315105139492119949588565)
              ·
                refine ⟨179473888353423280659241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 15315105139492119949588565 179473888353423280659241)
                ·
                  refine ⟨134605416265067460494431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179473888353423280659241 134605416265067460494431)
                  ·
                    rfl

theorem cell20_294911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 2].length) (baseStart_294911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294911 prefixEnd_294911 := by exact prefixLift 294911
  have htrace : WordTrace (prefixWord ++ tailWord_294911) baseStart_294911 baseEnd_294911 := by
    simpa [prefixWord, tailWord_294911, baseEnd_294911] using wordTrace_append hprefix tailTrace_294911
  have hstable : (prefixWord ++ tailWord_294911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294911).length < 2 ^ (prefixWord ++ tailWord_294911).sum := by decide
  have hdescent : baseEnd_294911 < baseStart_294911 := by decide
  rcases family_descends (prefixWord ++ tailWord_294911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294963 : List Nat := [1, 1, 1, 2, 4, 1, 3, 4, 3]
def baseStart_294963 : Nat := 118140960795 + 294963 * 2 ^ 59
def prefixEnd_294963 : Nat := 4983230072969 + 3 ^ 40 * 294963 * 2
def baseEnd_294963 : Nat := 134629150481986390760885

theorem tailTrace_294963 : CollatzResearch.WordTrace tailWord_294963 prefixEnd_294963 134629150481986390760885 := by
  unfold tailWord_294963
  simp only [CollatzResearch.WordTrace]
  refine ⟨10758184430406901514897543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7172122953604601009931695 10758184430406901514897543)
  ·
    refine ⟨16137276645610352272346315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10758184430406901514897543 16137276645610352272346315)
    ·
      refine ⟨24205914968415528408519473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16137276645610352272346315 24205914968415528408519473)
      ·
        refine ⟨18154436226311646306389605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24205914968415528408519473 18154436226311646306389605)
        ·
          refine ⟨3403956792433433682448051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18154436226311646306389605 3403956792433433682448051)
          ·
            refine ⟨5105935188650150523672077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3403956792433433682448051 5105935188650150523672077)
            ·
              refine ⟨1914725695743806446377029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5105935188650150523672077 1914725695743806446377029)
              ·
                refine ⟨359011067951963708695693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1914725695743806446377029 359011067951963708695693)
                ·
                  refine ⟨134629150481986390760885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359011067951963708695693 134629150481986390760885)
                  ·
                    rfl

theorem cell20_294963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 3].length) (baseStart_294963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294963 prefixEnd_294963 := by exact prefixLift 294963
  have htrace : WordTrace (prefixWord ++ tailWord_294963) baseStart_294963 baseEnd_294963 := by
    simpa [prefixWord, tailWord_294963, baseEnd_294963] using wordTrace_append hprefix tailTrace_294963
  have hstable : (prefixWord ++ tailWord_294963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294963).length < 2 ^ (prefixWord ++ tailWord_294963).sum := by decide
  have hdescent : baseEnd_294963 < baseStart_294963 := by decide
  rcases family_descends (prefixWord ++ tailWord_294963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_294970 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_294970 : Nat := 118140960795 + 294970 * 2 ^ 59
def prefixEnd_294970 : Nat := 4983230072969 + 3 ^ 40 * 294970 * 2
def baseEnd_294970 : Nat := 134632345472725477527523

theorem tailTrace_294970 : CollatzResearch.WordTrace tailWord_294970 prefixEnd_294970 134632345472725477527523 := by
  unfold tailWord_294970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2689609935345385427600591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7172293160921027806934909 2689609935345385427600591)
  ·
    refine ⟨4034414903018078141400887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2689609935345385427600591 4034414903018078141400887)
    ·
      refine ⟨6051622354527117212101331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4034414903018078141400887 6051622354527117212101331)
      ·
        refine ⟨9077433531790675818151997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6051622354527117212101331 9077433531790675818151997)
        ·
          refine ⟨3404037574421503431806999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9077433531790675818151997 3404037574421503431806999)
          ·
            refine ⟨5106056361632255147710499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3404037574421503431806999 5106056361632255147710499)
            ·
              refine ⟨7659084542448382721565749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5106056361632255147710499 7659084542448382721565749)
              ·
                refine ⟨718039175854535880146789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7659084542448382721565749 718039175854535880146789)
                ·
                  refine ⟨134632345472725477527523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 718039175854535880146789 134632345472725477527523)
                  ·
                    rfl

theorem cell20_294970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_294970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_294970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_294970 prefixEnd_294970 := by exact prefixLift 294970
  have htrace : WordTrace (prefixWord ++ tailWord_294970) baseStart_294970 baseEnd_294970 := by
    simpa [prefixWord, tailWord_294970, baseEnd_294970] using wordTrace_append hprefix tailTrace_294970
  have hstable : (prefixWord ++ tailWord_294970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_294970).length < 2 ^ (prefixWord ++ tailWord_294970).sum := by decide
  have hdescent : baseEnd_294970 < baseStart_294970 := by decide
  rcases family_descends (prefixWord ++ tailWord_294970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295004 : List Nat := [2, 2, 4, 1, 1, 2, 1, 5, 2]
def baseStart_295004 : Nat := 118140960795 + 295004 * 2 ^ 59
def prefixEnd_295004 : Nat := 4983230072969 + 3 ^ 40 * 295004 * 2
def baseEnd_295004 : Nat := 134647863999172470394051

theorem tailTrace_295004 : CollatzResearch.WordTrace tailWord_295004 prefixEnd_295004 134647863999172470394051 := by
  unfold tailWord_295004
  simp only [CollatzResearch.WordTrace]
  refine ⟨5379839911629182758570033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7173119882172243678093377 5379839911629182758570033)
  ·
    refine ⟨4034879933721887068927525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5379839911629182758570033 4034879933721887068927525)
    ·
      refine ⟨756539987572853825423911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4034879933721887068927525 756539987572853825423911)
      ·
        refine ⟨1134809981359280738135867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756539987572853825423911 1134809981359280738135867)
        ·
          refine ⟨1702214972038921107203801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1134809981359280738135867 1702214972038921107203801)
          ·
            refine ⟨1276661229029190830402851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1702214972038921107203801 1276661229029190830402851)
            ·
              refine ⟨1914991843543786245604277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276661229029190830402851 1914991843543786245604277)
              ·
                refine ⟨179530485332229960525401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1914991843543786245604277 179530485332229960525401)
                ·
                  refine ⟨134647863999172470394051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179530485332229960525401 134647863999172470394051)
                  ·
                    rfl

theorem cell20_295004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_295004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295004 prefixEnd_295004 := by exact prefixLift 295004
  have htrace : WordTrace (prefixWord ++ tailWord_295004) baseStart_295004 baseEnd_295004 := by
    simpa [prefixWord, tailWord_295004, baseEnd_295004] using wordTrace_append hprefix tailTrace_295004
  have hstable : (prefixWord ++ tailWord_295004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295004).length < 2 ^ (prefixWord ++ tailWord_295004).sum := by decide
  have hdescent : baseEnd_295004 < baseStart_295004 := by decide
  rcases family_descends (prefixWord ++ tailWord_295004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295015 : List Nat := [1, 1, 5, 1, 1, 2, 9]
def baseStart_295015 : Nat := 118140960795 + 295015 * 2 ^ 59
def prefixEnd_295015 : Nat := 4983230072969 + 3 ^ 40 * 295015 * 2
def baseEnd_295015 : Nat := 14961431633211702336371

theorem tailTrace_295015 : CollatzResearch.WordTrace tailWord_295015 prefixEnd_295015 14961431633211702336371 := by
  unfold tailWord_295015
  simp only [CollatzResearch.WordTrace]
  refine ⟨10760081026218514395790499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7173387350812342930526999 10760081026218514395790499)
  ·
    refine ⟨16140121539327771593685749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10760081026218514395790499 16140121539327771593685749)
    ·
      refine ⟨1513136394311978586908039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16140121539327771593685749 1513136394311978586908039)
      ·
        refine ⟨2269704591467967880362059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1513136394311978586908039 2269704591467967880362059)
        ·
          refine ⟨3404556887201951820543089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2269704591467967880362059 3404556887201951820543089)
          ·
            refine ⟨2553417665401463865407317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3404556887201951820543089 2553417665401463865407317)
            ·
              refine ⟨14961431633211702336371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2553417665401463865407317 14961431633211702336371)
              ·
                rfl

theorem cell20_295015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 9].length) (baseStart_295015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295015 prefixEnd_295015 := by exact prefixLift 295015
  have htrace : WordTrace (prefixWord ++ tailWord_295015) baseStart_295015 baseEnd_295015 := by
    simpa [prefixWord, tailWord_295015, baseEnd_295015] using wordTrace_append hprefix tailTrace_295015
  have hstable : (prefixWord ++ tailWord_295015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295015).length < 2 ^ (prefixWord ++ tailWord_295015).sum := by decide
  have hdescent : baseEnd_295015 < baseStart_295015 := by decide
  rcases family_descends (prefixWord ++ tailWord_295015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295018 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 5]
def baseStart_295018 : Nat := 118140960795 + 295018 * 2 ^ 59
def prefixEnd_295018 : Nat := 4983230072969 + 3 ^ 40 * 295018 * 2
def baseEnd_295018 : Nat := 134654253980650643927327

theorem tailTrace_295018 : CollatzResearch.WordTrace tailWord_295018 prefixEnd_295018 134654253980650643927327 := by
  unfold tailWord_295018
  simp only [CollatzResearch.WordTrace]
  refine ⟨2690047611301911477037427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7173460296805097272099805 2690047611301911477037427)
  ·
    refine ⟨4035071416952867215556141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2690047611301911477037427 4035071416952867215556141)
    ·
      refine ⟨1513151781357325205833553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4035071416952867215556141 1513151781357325205833553)
      ·
        refine ⟨1134863836017993904375165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1513151781357325205833553 1134863836017993904375165)
        ·
          refine ⟨425573938506747714140687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1134863836017993904375165 425573938506747714140687)
          ·
            refine ⟨638360907760121571211031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425573938506747714140687 638360907760121571211031)
            ·
              refine ⟨957541361640182356816547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638360907760121571211031 957541361640182356816547)
              ·
                refine ⟨1436312042460273535224821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957541361640182356816547 1436312042460273535224821)
                ·
                  refine ⟨134654253980650643927327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1436312042460273535224821 134654253980650643927327)
                  ·
                    rfl

theorem cell20_295018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_295018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295018 prefixEnd_295018 := by exact prefixLift 295018
  have htrace : WordTrace (prefixWord ++ tailWord_295018) baseStart_295018 baseEnd_295018 := by
    simpa [prefixWord, tailWord_295018, baseEnd_295018] using wordTrace_append hprefix tailTrace_295018
  have hstable : (prefixWord ++ tailWord_295018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295018).length < 2 ^ (prefixWord ++ tailWord_295018).sum := by decide
  have hdescent : baseEnd_295018 < baseStart_295018 := by decide
  rcases family_descends (prefixWord ++ tailWord_295018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295025 : List Nat := [1, 2, 2, 2, 1, 1, 3, 6, 2]
def baseStart_295025 : Nat := 118140960795 + 295025 * 2 ^ 59
def prefixEnd_295025 : Nat := 4983230072969 + 3 ^ 40 * 295025 * 2
def baseEnd_295025 : Nat := 134657448971389730693965

theorem tailTrace_295025 : CollatzResearch.WordTrace tailWord_295025 prefixEnd_295025 134657448971389730693965 := by
  unfold tailWord_295025
  simp only [CollatzResearch.WordTrace]
  refine ⟨10760445756182286103654529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7173630504121524069103019 10760445756182286103654529)
  ·
    refine ⟨8070334317136714577740897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10760445756182286103654529 8070334317136714577740897)
    ·
      refine ⟨6052750737852535933305673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8070334317136714577740897 6052750737852535933305673)
      ·
        refine ⟨4539563053389401949979255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6052750737852535933305673 4539563053389401949979255)
        ·
          refine ⟨6809344580084102924968883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4539563053389401949979255 6809344580084102924968883)
          ·
            refine ⟨10214016870126154387453325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6809344580084102924968883 10214016870126154387453325)
            ·
              refine ⟨3830256326297307895294997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10214016870126154387453325 3830256326297307895294997)
              ·
                refine ⟨179543265295186307591953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3830256326297307895294997 179543265295186307591953)
                ·
                  refine ⟨134657448971389730693965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179543265295186307591953 134657448971389730693965)
                  ·
                    rfl

theorem cell20_295025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 2].length) (baseStart_295025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295025 prefixEnd_295025 := by exact prefixLift 295025
  have htrace : WordTrace (prefixWord ++ tailWord_295025) baseStart_295025 baseEnd_295025 := by
    simpa [prefixWord, tailWord_295025, baseEnd_295025] using wordTrace_append hprefix tailTrace_295025
  have hstable : (prefixWord ++ tailWord_295025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295025).length < 2 ^ (prefixWord ++ tailWord_295025).sum := by decide
  have hdescent : baseEnd_295025 < baseStart_295025 := by decide
  rcases family_descends (prefixWord ++ tailWord_295025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295062 : List Nat := [5, 3, 2, 1, 1, 2, 6]
def baseStart_295062 : Nat := 118140960795 + 295062 * 2 ^ 59
def prefixEnd_295062 : Nat := 4983230072969 + 3 ^ 40 * 295062 * 2
def baseEnd_295062 : Nat := 14963815197731338495609

theorem tailTrace_295062 : CollatzResearch.WordTrace tailWord_295062 prefixEnd_295062 14963815197731338495609 := by
  unfold tailWord_295062
  simp only [CollatzResearch.WordTrace]
  refine ⟨672612203565515088921965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7174530171365494281834293 672612203565515088921965)
  ·
    refine ⟨252229576337068158345737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 672612203565515088921965 252229576337068158345737)
    ·
      refine ⟨189172182252801118759303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252229576337068158345737 189172182252801118759303)
      ·
        refine ⟨283758273379201678138955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189172182252801118759303 283758273379201678138955)
        ·
          refine ⟨425637410068802517208433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283758273379201678138955 425637410068802517208433)
          ·
            refine ⟨319228057551601887906325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 425637410068802517208433 319228057551601887906325)
            ·
              refine ⟨14963815197731338495609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 319228057551601887906325 14963815197731338495609)
              ·
                rfl

theorem cell20_295062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 6].length) (baseStart_295062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295062 prefixEnd_295062 := by exact prefixLift 295062
  have htrace : WordTrace (prefixWord ++ tailWord_295062) baseStart_295062 baseEnd_295062 := by
    simpa [prefixWord, tailWord_295062, baseEnd_295062] using wordTrace_append hprefix tailTrace_295062
  have hstable : (prefixWord ++ tailWord_295062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295062).length < 2 ^ (prefixWord ++ tailWord_295062).sum := by decide
  have hdescent : baseEnd_295062 < baseStart_295062 := by decide
  rcases family_descends (prefixWord ++ tailWord_295062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295077 : List Nat := [1, 3, 1, 2, 1, 3, 2, 4, 3]
def baseStart_295077 : Nat := 118140960795 + 295077 * 2 ^ 59
def prefixEnd_295077 : Nat := 4983230072969 + 3 ^ 40 * 295077 * 2
def baseEnd_295077 : Nat := 134681183188308660960419

theorem tailTrace_295077 : CollatzResearch.WordTrace tailWord_295077 prefixEnd_295077 134681183188308660960419 := by
  unfold tailWord_295077
  simp only [CollatzResearch.WordTrace]
  refine ⟨10762342351993898984547485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7174894901329265989698323 10762342351993898984547485)
  ·
    refine ⟨4035878381997712119205307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10762342351993898984547485 4035878381997712119205307)
    ·
      refine ⟨6053817572996568178807961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4035878381997712119205307 6053817572996568178807961)
      ·
        refine ⟨4540363179747426134105971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6053817572996568178807961 4540363179747426134105971)
        ·
          refine ⟨6810544769621139201158957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4540363179747426134105971 6810544769621139201158957)
          ·
            refine ⟨2553954288607927200434609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6810544769621139201158957 2553954288607927200434609)
            ·
              refine ⟨1915465716455945400325957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2553954288607927200434609 1915465716455945400325957)
              ·
                refine ⟨359149821835489762561117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1915465716455945400325957 359149821835489762561117)
                ·
                  refine ⟨134681183188308660960419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359149821835489762561117 134681183188308660960419)
                  ·
                    rfl

theorem cell20_295077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_295077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295077 prefixEnd_295077 := by exact prefixLift 295077
  have htrace : WordTrace (prefixWord ++ tailWord_295077) baseStart_295077 baseEnd_295077 := by
    simpa [prefixWord, tailWord_295077, baseEnd_295077] using wordTrace_append hprefix tailTrace_295077
  have hstable : (prefixWord ++ tailWord_295077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295077).length < 2 ^ (prefixWord ++ tailWord_295077).sum := by decide
  have hdescent : baseEnd_295077 < baseStart_295077 := by decide
  rcases family_descends (prefixWord ++ tailWord_295077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295086 : List Nat := [4, 1, 4, 2, 2, 1, 2, 1, 3]
def baseStart_295086 : Nat := 118140960795 + 295086 * 2 ^ 59
def prefixEnd_295086 : Nat := 4983230072969 + 3 ^ 40 * 295086 * 2
def baseEnd_295086 : Nat := 134685291033544629660383

theorem tailTrace_295086 : CollatzResearch.WordTrace tailWord_295086 prefixEnd_295086 134685291033544629660383 := by
  unfold tailWord_295086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1345333826120161690203139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7175113739307529014416741 1345333826120161690203139)
  ·
    refine ⟨2018000739180242535304709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1345333826120161690203139 2018000739180242535304709)
    ·
      refine ⟨378375138596295475369633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2018000739180242535304709 378375138596295475369633)
      ·
        refine ⟨283781353947221606527225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378375138596295475369633 283781353947221606527225)
        ·
          refine ⟨212836015460416204895419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283781353947221606527225 212836015460416204895419)
          ·
            refine ⟨319254023190624307343129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212836015460416204895419 319254023190624307343129)
            ·
              refine ⟨239440517392968230507347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319254023190624307343129 239440517392968230507347)
              ·
                refine ⟨359160776089452345761021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239440517392968230507347 359160776089452345761021)
                ·
                  refine ⟨134685291033544629660383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359160776089452345761021 134685291033544629660383)
                  ·
                    rfl

theorem cell20_295086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_295086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295086 prefixEnd_295086 := by exact prefixLift 295086
  have htrace : WordTrace (prefixWord ++ tailWord_295086) baseStart_295086 baseEnd_295086 := by
    simpa [prefixWord, tailWord_295086, baseEnd_295086] using wordTrace_append hprefix tailTrace_295086
  have hstable : (prefixWord ++ tailWord_295086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295086).length < 2 ^ (prefixWord ++ tailWord_295086).sum := by decide
  have hdescent : baseEnd_295086 < baseStart_295086 := by decide
  rcases family_descends (prefixWord ++ tailWord_295086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295108 : List Nat := [2, 3, 3, 1, 2, 1, 2, 6]
def baseStart_295108 : Nat := 118140960795 + 295108 * 2 ^ 59
def prefixEnd_295108 : Nat := 4983230072969 + 3 ^ 40 * 295108 * 2
def baseEnd_295108 : Nat := 44898444144336776975653

theorem tailTrace_295108 : CollatzResearch.WordTrace tailWord_295108 prefixEnd_295108 44898444144336776975653 := by
  unfold tailWord_295108
  simp only [CollatzResearch.WordTrace]
  refine ⟨5381736507440795639462989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7175648676587727519283985 5381736507440795639462989)
  ·
    refine ⟨2018151190290298364798621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5381736507440795639462989 2018151190290298364798621)
    ·
      refine ⟨756806696358861886799483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2018151190290298364798621 756806696358861886799483)
      ·
        refine ⟨1135210044538292830199225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 756806696358861886799483 1135210044538292830199225)
        ·
          refine ⟨851407533403719622649419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1135210044538292830199225 851407533403719622649419)
          ·
            refine ⟨1277111300105579433974129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851407533403719622649419 1277111300105579433974129)
            ·
              refine ⟨957833475079184575480597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1277111300105579433974129 957833475079184575480597)
              ·
                refine ⟨44898444144336776975653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 957833475079184575480597 44898444144336776975653)
                ·
                  rfl

theorem cell20_295108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_295108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295108 prefixEnd_295108 := by exact prefixLift 295108
  have htrace : WordTrace (prefixWord ++ tailWord_295108) baseStart_295108 baseEnd_295108 := by
    simpa [prefixWord, tailWord_295108, baseEnd_295108] using wordTrace_append hprefix tailTrace_295108
  have hstable : (prefixWord ++ tailWord_295108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295108).length < 2 ^ (prefixWord ++ tailWord_295108).sum := by decide
  have hdescent : baseEnd_295108 < baseStart_295108 := by decide
  rcases family_descends (prefixWord ++ tailWord_295108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295138 : List Nat := [3, 3, 4, 1, 2, 1, 1, 5]
def baseStart_295138 : Nat := 118140960795 + 295138 * 2 ^ 59
def prefixEnd_295138 : Nat := 4983230072969 + 3 ^ 40 * 295138 * 2
def baseEnd_295138 : Nat := 44903008416821186642279

theorem tailTrace_295138 : CollatzResearch.WordTrace tailWord_295138 prefixEnd_295138 44903008416821186642279 := by
  unfold tailWord_295138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2691141801193226600629517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7176378136515270935012045 2691141801193226600629517)
  ·
    refine ⟨1009178175447459975236069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2691141801193226600629517 1009178175447459975236069)
    ·
      refine ⟨189220907896398745356763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1009178175447459975236069 189220907896398745356763)
      ·
        refine ⟨283831361844598118035145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189220907896398745356763 283831361844598118035145)
        ·
          refine ⟨212873521383448588526359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283831361844598118035145 212873521383448588526359)
          ·
            refine ⟨319310282075172882789539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212873521383448588526359 319310282075172882789539)
            ·
              refine ⟨478965423112759324184309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319310282075172882789539 478965423112759324184309)
              ·
                refine ⟨44903008416821186642279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 478965423112759324184309 44903008416821186642279)
                ·
                  rfl

theorem cell20_295138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_295138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295138 prefixEnd_295138 := by exact prefixLift 295138
  have htrace : WordTrace (prefixWord ++ tailWord_295138) baseStart_295138 baseEnd_295138 := by
    simpa [prefixWord, tailWord_295138, baseEnd_295138] using wordTrace_append hprefix tailTrace_295138
  have hstable : (prefixWord ++ tailWord_295138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295138).length < 2 ^ (prefixWord ++ tailWord_295138).sum := by decide
  have hdescent : baseEnd_295138 < baseStart_295138 := by decide
  rcases family_descends (prefixWord ++ tailWord_295138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295153 : List Nat := [1, 2, 2, 2, 2, 1, 4, 3, 3]
def baseStart_295153 : Nat := 118140960795 + 295153 * 2 ^ 59
def prefixEnd_295153 : Nat := 4983230072969 + 3 ^ 40 * 295153 * 2
def baseEnd_295153 : Nat := 134715871659190174426775

theorem tailTrace_295153 : CollatzResearch.WordTrace tailWord_295153 prefixEnd_295153 134715871659190174426775 := by
  unfold tailWord_295153
  simp only [CollatzResearch.WordTrace]
  refine ⟨10765114299718563964314113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7176742866479042642876075 10765114299718563964314113)
  ·
    refine ⟨8073835724788922973235585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10765114299718563964314113 8073835724788922973235585)
    ·
      refine ⟨6055376793591692229926689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8073835724788922973235585 6055376793591692229926689)
      ·
        refine ⟨4541532595193769172445017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6055376793591692229926689 4541532595193769172445017)
        ·
          refine ⟨3406149446395326879333763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4541532595193769172445017 3406149446395326879333763)
          ·
            refine ⟨5109224169592990319000645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3406149446395326879333763 5109224169592990319000645)
            ·
              refine ⟨957979531798685684812621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5109224169592990319000645 957979531798685684812621)
              ·
                refine ⟨359242324424507131804733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 957979531798685684812621 359242324424507131804733)
                ·
                  refine ⟨134715871659190174426775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359242324424507131804733 134715871659190174426775)
                  ·
                    rfl

theorem cell20_295153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_295153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295153 prefixEnd_295153 := by exact prefixLift 295153
  have htrace : WordTrace (prefixWord ++ tailWord_295153) baseStart_295153 baseEnd_295153 := by
    simpa [prefixWord, tailWord_295153, baseEnd_295153] using wordTrace_append hprefix tailTrace_295153
  have hstable : (prefixWord ++ tailWord_295153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295153).length < 2 ^ (prefixWord ++ tailWord_295153).sum := by decide
  have hdescent : baseEnd_295153 < baseStart_295153 := by decide
  rcases family_descends (prefixWord ++ tailWord_295153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295177 : List Nat := [1, 2, 1, 1, 3, 4, 1, 5, 2]
def baseStart_295177 : Nat := 118140960795 + 295177 * 2 ^ 59
def prefixEnd_295177 : Nat := 4983230072969 + 3 ^ 40 * 295177 * 2
def baseEnd_295177 : Nat := 134726825913152757626677

theorem tailTrace_295177 : CollatzResearch.WordTrace tailWord_295177 prefixEnd_295177 134726825913152757626677 := by
  unfold tailWord_295177
  simp only [CollatzResearch.WordTrace]
  refine ⟨10765989651631616063187785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7177326434421077375458523 10765989651631616063187785)
  ·
    refine ⟨8074492238723712047390839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10765989651631616063187785 8074492238723712047390839)
    ·
      refine ⟨12111738358085568071086259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8074492238723712047390839 12111738358085568071086259)
      ·
        refine ⟨18167607537128352106629389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12111738358085568071086259 18167607537128352106629389)
        ·
          refine ⟨6812852826423132039986021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18167607537128352106629389 6812852826423132039986021)
          ·
            refine ⟨1277409904954337257497379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6812852826423132039986021 1277409904954337257497379)
            ·
              refine ⟨1916114857431505886246069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277409904954337257497379 1916114857431505886246069)
              ·
                refine ⟨179635767884203676835569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1916114857431505886246069 179635767884203676835569)
                ·
                  refine ⟨134726825913152757626677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179635767884203676835569 134726825913152757626677)
                  ·
                    rfl

theorem cell20_295177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 2].length) (baseStart_295177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295177 prefixEnd_295177 := by exact prefixLift 295177
  have htrace : WordTrace (prefixWord ++ tailWord_295177) baseStart_295177 baseEnd_295177 := by
    simpa [prefixWord, tailWord_295177, baseEnd_295177] using wordTrace_append hprefix tailTrace_295177
  have hstable : (prefixWord ++ tailWord_295177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295177).length < 2 ^ (prefixWord ++ tailWord_295177).sum := by decide
  have hdescent : baseEnd_295177 < baseStart_295177 := by decide
  rcases family_descends (prefixWord ++ tailWord_295177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295191 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 5]
def baseStart_295191 : Nat := 118140960795 + 295191 * 2 ^ 59
def prefixEnd_295191 : Nat := 4983230072969 + 3 ^ 40 * 295191 * 2
def baseEnd_295191 : Nat := 134733215894630931159953

theorem tailTrace_295191 : CollatzResearch.WordTrace tailWord_295191 prefixEnd_295191 134733215894630931159953 := by
  unfold tailWord_295191
  simp only [CollatzResearch.WordTrace]
  refine ⟨10766500273580896454197427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7177666849053930969464951 10766500273580896454197427)
  ·
    refine ⟨16149750410371344681296141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10766500273580896454197427 16149750410371344681296141)
    ·
      refine ⟨6056156403889254255486053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16149750410371344681296141 6056156403889254255486053)
      ·
        refine ⟨1135529325729235172903635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6056156403889254255486053 1135529325729235172903635)
        ·
          refine ⟨1703293988593852759355453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1135529325729235172903635 1703293988593852759355453)
          ·
            refine ⟨638735245722694784758295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1703293988593852759355453 638735245722694784758295)
            ·
              refine ⟨958102868584042177137443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 638735245722694784758295 958102868584042177137443)
              ·
                refine ⟨1437154302876063265706165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 958102868584042177137443 1437154302876063265706165)
                ·
                  refine ⟨134733215894630931159953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1437154302876063265706165 134733215894630931159953)
                  ·
                    rfl

theorem cell20_295191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_295191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295191 prefixEnd_295191 := by exact prefixLift 295191
  have htrace : WordTrace (prefixWord ++ tailWord_295191) baseStart_295191 baseEnd_295191 := by
    simpa [prefixWord, tailWord_295191, baseEnd_295191] using wordTrace_append hprefix tailTrace_295191
  have hstable : (prefixWord ++ tailWord_295191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295191).length < 2 ^ (prefixWord ++ tailWord_295191).sum := by decide
  have hdescent : baseEnd_295191 < baseStart_295191 := by decide
  rcases family_descends (prefixWord ++ tailWord_295191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295218 : List Nat := [3, 2, 1, 1, 6, 1, 2, 4]
def baseStart_295218 : Nat := 118140960795 + 295218 * 2 ^ 59
def prefixEnd_295218 : Nat := 4983230072969 + 3 ^ 40 * 295218 * 2
def baseEnd_295218 : Nat := 44915179810112945753281

theorem tailTrace_295218 : CollatzResearch.WordTrace tailWord_295218 prefixEnd_295218 44915179810112945753281 := by
  unfold tailWord_295218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2691871261120770016357577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7178323362988720043620205 2691871261120770016357577)
  ·
    refine ⟨2018903445840577512268183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2691871261120770016357577 2018903445840577512268183)
    ·
      refine ⟨3028355168760866268402275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2018903445840577512268183 3028355168760866268402275)
      ·
        refine ⟨4542532753141299402603413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3028355168760866268402275 4542532753141299402603413)
        ·
          refine ⟨212931222803498409497035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4542532753141299402603413 212931222803498409497035)
          ·
            refine ⟨319396834205247614245553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212931222803498409497035 319396834205247614245553)
            ·
              refine ⟨239547625653935710684165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319396834205247614245553 239547625653935710684165)
              ·
                refine ⟨44915179810112945753281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239547625653935710684165 44915179810112945753281)
                ·
                  rfl

theorem cell20_295218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_295218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295218 prefixEnd_295218 := by exact prefixLift 295218
  have htrace : WordTrace (prefixWord ++ tailWord_295218) baseStart_295218 baseEnd_295218 := by
    simpa [prefixWord, tailWord_295218, baseEnd_295218] using wordTrace_append hprefix tailTrace_295218
  have hstable : (prefixWord ++ tailWord_295218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295218).length < 2 ^ (prefixWord ++ tailWord_295218).sum := by decide
  have hdescent : baseEnd_295218 < baseStart_295218 := by decide
  rcases family_descends (prefixWord ++ tailWord_295218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295267 : List Nat := [1, 1, 1, 5, 2, 1, 3, 3, 3]
def baseStart_295267 : Nat := 118140960795 + 295267 * 2 ^ 59
def prefixEnd_295267 : Nat := 4983230072969 + 3 ^ 40 * 295267 * 2
def baseEnd_295267 : Nat := 134767904365512444626309

theorem tailTrace_295267 : CollatzResearch.WordTrace tailWord_295267 prefixEnd_295267 134767904365512444626309 := by
  unfold tailWord_295267
  simp only [CollatzResearch.WordTrace]
  refine ⟨10769272221305561433964055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7179514814203707622642703 10769272221305561433964055)
  ·
    refine ⟨16153908331958342150946083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10769272221305561433964055 16153908331958342150946083)
    ·
      refine ⟨24230862497937513226419125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16153908331958342150946083 24230862497937513226419125)
      ·
        refine ⟨2271643359181641864976793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24230862497937513226419125 2271643359181641864976793)
        ·
          refine ⟨1703732519386231398732595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2271643359181641864976793 1703732519386231398732595)
          ·
            refine ⟨2555598779079347098098893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703732519386231398732595 2555598779079347098098893)
            ·
              refine ⟨958349542154755161787085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2555598779079347098098893 958349542154755161787085)
              ·
                refine ⟨359381078308033185670157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 958349542154755161787085 359381078308033185670157)
                ·
                  refine ⟨134767904365512444626309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359381078308033185670157 134767904365512444626309)
                  ·
                    rfl

theorem cell20_295267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 3].length) (baseStart_295267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295267 prefixEnd_295267 := by exact prefixLift 295267
  have htrace : WordTrace (prefixWord ++ tailWord_295267) baseStart_295267 baseEnd_295267 := by
    simpa [prefixWord, tailWord_295267, baseEnd_295267] using wordTrace_append hprefix tailTrace_295267
  have hstable : (prefixWord ++ tailWord_295267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295267).length < 2 ^ (prefixWord ++ tailWord_295267).sum := by decide
  have hdescent : baseEnd_295267 < baseStart_295267 := by decide
  rcases family_descends (prefixWord ++ tailWord_295267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295295 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 6]
def baseStart_295295 : Nat := 118140960795 + 295295 * 2 ^ 59
def prefixEnd_295295 : Nat := 4983230072969 + 3 ^ 40 * 295295 * 2
def baseEnd_295295 : Nat := 134780684328468791692861

theorem tailTrace_295295 : CollatzResearch.WordTrace tailWord_295295 prefixEnd_295295 134780684328468791692861 := by
  unfold tailWord_295295
  simp only [CollatzResearch.WordTrace]
  refine ⟨10770293465204122215983339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7180195643469414810655559 10770293465204122215983339)
  ·
    refine ⟨16155440197806183323975009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10770293465204122215983339 16155440197806183323975009)
    ·
      refine ⟨12116580148354637492981257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16155440197806183323975009 12116580148354637492981257)
      ·
        refine ⟨9087435111265978119735943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12116580148354637492981257 9087435111265978119735943)
        ·
          refine ⟨13631152666898967179603915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9087435111265978119735943 13631152666898967179603915)
          ·
            refine ⟨20446729000348450769405873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13631152666898967179603915 20446729000348450769405873)
            ·
              refine ⟨15335046750261338077054405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20446729000348450769405873 15335046750261338077054405)
              ·
                refine ⟨2875321265674000889447701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15335046750261338077054405 2875321265674000889447701)
                ·
                  refine ⟨134780684328468791692861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2875321265674000889447701 134780684328468791692861)
                  ·
                    rfl

theorem cell20_295295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_295295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295295 prefixEnd_295295 := by exact prefixLift 295295
  have htrace : WordTrace (prefixWord ++ tailWord_295295) baseStart_295295 baseEnd_295295 := by
    simpa [prefixWord, tailWord_295295, baseEnd_295295] using wordTrace_append hprefix tailTrace_295295
  have hstable : (prefixWord ++ tailWord_295295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295295).length < 2 ^ (prefixWord ++ tailWord_295295).sum := by decide
  have hdescent : baseEnd_295295 < baseStart_295295 := by decide
  rcases family_descends (prefixWord ++ tailWord_295295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295298 : List Nat := [3, 4, 2, 1, 10]
def baseStart_295298 : Nat := 118140960795 + 295298 * 2 ^ 59
def prefixEnd_295298 : Nat := 4983230072969 + 3 ^ 40 * 295298 * 2
def baseEnd_295298 : Nat := 1663975970496470550529

theorem tailTrace_295298 : CollatzResearch.WordTrace tailWord_295298 prefixEnd_295298 1663975970496470550529 := by
  unfold tailWord_295298
  simp only [CollatzResearch.WordTrace]
  refine ⟨2692600721048313432085637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7180268589462169152228365 2692600721048313432085637)
  ·
    refine ⟨504862635196558768516057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2692600721048313432085637 504862635196558768516057)
    ·
      refine ⟨378646976397419076387043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 504862635196558768516057 378646976397419076387043)
      ·
        refine ⟨567970464596128614580565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378646976397419076387043 567970464596128614580565)
        ·
          refine ⟨1663975970496470550529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 567970464596128614580565 1663975970496470550529)
          ·
            rfl

theorem cell20_295298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 10].length) (baseStart_295298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295298 prefixEnd_295298 := by exact prefixLift 295298
  have htrace : WordTrace (prefixWord ++ tailWord_295298) baseStart_295298 baseEnd_295298 := by
    simpa [prefixWord, tailWord_295298, baseEnd_295298] using wordTrace_append hprefix tailTrace_295298
  have hstable : (prefixWord ++ tailWord_295298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295298).length < 2 ^ (prefixWord ++ tailWord_295298).sum := by decide
  have hdescent : baseEnd_295298 < baseStart_295298 := by decide
  rcases family_descends (prefixWord ++ tailWord_295298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295305 : List Nat := [1, 2, 1, 1, 6, 1, 1, 4, 3]
def baseStart_295305 : Nat := 118140960795 + 295305 * 2 ^ 59
def prefixEnd_295305 : Nat := 4983230072969 + 3 ^ 40 * 295305 * 2
def baseEnd_295305 : Nat := 134785248600953201359487

theorem tailTrace_295305 : CollatzResearch.WordTrace tailWord_295305 prefixEnd_295305 134785248600953201359487 := by
  unfold tailWord_295305
  simp only [CollatzResearch.WordTrace]
  refine ⟨10770658195167893923847369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7180438796778595949231579 10770658195167893923847369)
  ·
    refine ⟨8077993646375920442885527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10770658195167893923847369 8077993646375920442885527)
    ·
      refine ⟨12116990469563880664328291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8077993646375920442885527 12116990469563880664328291)
      ·
        refine ⟨18175485704345820996492437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12116990469563880664328291 18175485704345820996492437)
        ·
          refine ⟨851975892391210359210583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18175485704345820996492437 851975892391210359210583)
          ·
            refine ⟨1277963838586815538815875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851975892391210359210583 1277963838586815538815875)
            ·
              refine ⟨1916945757880223308223813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277963838586815538815875 1916945757880223308223813)
              ·
                refine ⟨359427329602541870291965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1916945757880223308223813 359427329602541870291965)
                ·
                  refine ⟨134785248600953201359487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359427329602541870291965 134785248600953201359487)
                  ·
                    rfl

theorem cell20_295305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_295305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295305 prefixEnd_295305 := by exact prefixLift 295305
  have htrace : WordTrace (prefixWord ++ tailWord_295305) baseStart_295305 baseEnd_295305 := by
    simpa [prefixWord, tailWord_295305, baseEnd_295305] using wordTrace_append hprefix tailTrace_295305
  have hstable : (prefixWord ++ tailWord_295305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295305).length < 2 ^ (prefixWord ++ tailWord_295305).sum := by decide
  have hdescent : baseEnd_295305 < baseStart_295305 := by decide
  rcases family_descends (prefixWord ++ tailWord_295305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295308 : List Nat := [2, 2, 1, 2, 1, 4, 4, 2, 2]
def baseStart_295308 : Nat := 118140960795 + 295308 * 2 ^ 59
def prefixEnd_295308 : Nat := 4983230072969 + 3 ^ 40 * 295308 * 2
def baseEnd_295308 : Nat := 134786617882698524259475

theorem tailTrace_295308 : CollatzResearch.WordTrace tailWord_295308 prefixEnd_295308 134786617882698524259475 := by
  unfold tailWord_295308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5385383807078512718103289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7180511742771350290804385 5385383807078512718103289)
  ·
    refine ⟨4039037855308884538577467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5385383807078512718103289 4039037855308884538577467)
    ·
      refine ⟨6058556782963326807866201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4039037855308884538577467 6058556782963326807866201)
      ·
        refine ⟨4543917587222495105899651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6058556782963326807866201 4543917587222495105899651)
        ·
          refine ⟨6815876380833742658849477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4543917587222495105899651 6815876380833742658849477)
          ·
            refine ⟨1277976821406326748534277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6815876380833742658849477 1277976821406326748534277)
            ·
              refine ⟨239620654013686265350177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1277976821406326748534277 239620654013686265350177)
              ·
                refine ⟨179715490510264699012633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239620654013686265350177 179715490510264699012633)
                ·
                  refine ⟨134786617882698524259475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179715490510264699012633 134786617882698524259475)
                  ·
                    rfl

theorem cell20_295308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 2, 2].length) (baseStart_295308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295308 prefixEnd_295308 := by exact prefixLift 295308
  have htrace : WordTrace (prefixWord ++ tailWord_295308) baseStart_295308 baseEnd_295308 := by
    simpa [prefixWord, tailWord_295308, baseEnd_295308] using wordTrace_append hprefix tailTrace_295308
  have hstable : (prefixWord ++ tailWord_295308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295308).length < 2 ^ (prefixWord ++ tailWord_295308).sum := by decide
  have hdescent : baseEnd_295308 < baseStart_295308 := by decide
  rcases family_descends (prefixWord ++ tailWord_295308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295319 : List Nat := [1, 1, 3, 3, 1, 1, 5, 5]
def baseStart_295319 : Nat := 118140960795 + 295319 * 2 ^ 59
def prefixEnd_295319 : Nat := 4983230072969 + 3 ^ 40 * 295319 * 2
def baseEnd_295319 : Nat := 44930546194143791630921

theorem tailTrace_295319 : CollatzResearch.WordTrace tailWord_295319 prefixEnd_295319 44930546194143791630921 := by
  unfold tailWord_295319
  simp only [CollatzResearch.WordTrace]
  refine ⟨10771168817117174314857011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7180779211411449543238007 10771168817117174314857011)
  ·
    refine ⟨16156753225675761472285517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10771168817117174314857011 16156753225675761472285517)
    ·
      refine ⟨6058782459628410552107069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16156753225675761472285517 6058782459628410552107069)
      ·
        refine ⟨2272043422360653957040151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6058782459628410552107069 2272043422360653957040151)
        ·
          refine ⟨3408065133540980935560227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2272043422360653957040151 3408065133540980935560227)
          ·
            refine ⟨5112097700311471403340341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3408065133540980935560227 5112097700311471403340341)
            ·
              refine ⟨479259159404200444063157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5112097700311471403340341 479259159404200444063157)
              ·
                refine ⟨44930546194143791630921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 479259159404200444063157 44930546194143791630921)
                ·
                  rfl

theorem cell20_295319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 5].length) (baseStart_295319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295319 prefixEnd_295319 := by exact prefixLift 295319
  have htrace : WordTrace (prefixWord ++ tailWord_295319) baseStart_295319 baseEnd_295319 := by
    simpa [prefixWord, tailWord_295319, baseEnd_295319] using wordTrace_append hprefix tailTrace_295319
  have hstable : (prefixWord ++ tailWord_295319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295319).length < 2 ^ (prefixWord ++ tailWord_295319).sum := by decide
  have hdescent : baseEnd_295319 < baseStart_295319 := by decide
  rcases family_descends (prefixWord ++ tailWord_295319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295357 : List Nat := [1, 4, 1, 2, 2, 3, 7]
def baseStart_295357 : Nat := 118140960795 + 295357 * 2 ^ 59
def prefixEnd_295357 : Nat := 4983230072969 + 3 ^ 40 * 295357 * 2
def baseEnd_295357 : Nat := 14978775868652459069549

theorem tailTrace_295357 : CollatzResearch.WordTrace tailWord_295357 prefixEnd_295357 14978775868652459069549 := by
  unfold tailWord_295357
  simp only [CollatzResearch.WordTrace]
  refine ⟨10772554790979506804740325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7181703193986337869826883 10772554790979506804740325)
  ·
    refine ⟨2019854023308657525888811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10772554790979506804740325 2019854023308657525888811)
    ·
      refine ⟨3029781034962986288833217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2019854023308657525888811 3029781034962986288833217)
      ·
        refine ⟨2272335776222239716624913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3029781034962986288833217 2272335776222239716624913)
        ·
          refine ⟨1704251832166679787468685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2272335776222239716624913 1704251832166679787468685)
          ·
            refine ⟨639094437062504920300757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1704251832166679787468685 639094437062504920300757)
            ·
              refine ⟨14978775868652459069549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 639094437062504920300757 14978775868652459069549)
              ·
                rfl

theorem cell20_295357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 7].length) (baseStart_295357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295357 prefixEnd_295357 := by exact prefixLift 295357
  have htrace : WordTrace (prefixWord ++ tailWord_295357) baseStart_295357 baseEnd_295357 := by
    simpa [prefixWord, tailWord_295357, baseEnd_295357] using wordTrace_append hprefix tailTrace_295357
  have hstable : (prefixWord ++ tailWord_295357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295357).length < 2 ^ (prefixWord ++ tailWord_295357).sum := by decide
  have hdescent : baseEnd_295357 < baseStart_295357 := by decide
  rcases family_descends (prefixWord ++ tailWord_295357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295367 : List Nat := [1, 1, 4, 1, 1, 4, 2, 4, 2]
def baseStart_295367 : Nat := 118140960795 + 295367 * 2 ^ 59
def prefixEnd_295367 : Nat := 4983230072969 + 3 ^ 40 * 295367 * 2
def baseEnd_295367 : Nat := 134813547090356541292567

theorem tailTrace_295367 : CollatzResearch.WordTrace tailWord_295367 prefixEnd_295367 134813547090356541292567 := by
  unfold tailWord_295367
  simp only [CollatzResearch.WordTrace]
  refine ⟨10772919520943278512604355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7181946347295519008402903 10772919520943278512604355)
  ·
    refine ⟨16159379281414917768906533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10772919520943278512604355 16159379281414917768906533)
    ·
      refine ⟨3029883615265297081669975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16159379281414917768906533 3029883615265297081669975)
      ·
        refine ⟨4544825422897945622504963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3029883615265297081669975 4544825422897945622504963)
        ·
          refine ⟨6817238134346918433757445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4544825422897945622504963 6817238134346918433757445)
          ·
            refine ⟨1278232150190047206329521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6817238134346918433757445 1278232150190047206329521)
            ·
              refine ⟨958674112642535404747141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1278232150190047206329521 958674112642535404747141)
              ·
                refine ⟨179751396120475388390089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 958674112642535404747141 179751396120475388390089)
                ·
                  refine ⟨134813547090356541292567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179751396120475388390089 134813547090356541292567)
                  ·
                    rfl

theorem cell20_295367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 2].length) (baseStart_295367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295367 prefixEnd_295367 := by exact prefixLift 295367
  have htrace : WordTrace (prefixWord ++ tailWord_295367) baseStart_295367 baseEnd_295367 := by
    simpa [prefixWord, tailWord_295367, baseEnd_295367] using wordTrace_append hprefix tailTrace_295367
  have hstable : (prefixWord ++ tailWord_295367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295367).length < 2 ^ (prefixWord ++ tailWord_295367).sum := by decide
  have hdescent : baseEnd_295367 < baseStart_295367 := by decide
  rcases family_descends (prefixWord ++ tailWord_295367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295436 : List Nat := [2, 2, 1, 2, 4, 1, 4, 1, 3]
def baseStart_295436 : Nat := 118140960795 + 295436 * 2 ^ 59
def prefixEnd_295436 : Nat := 4983230072969 + 3 ^ 40 * 295436 * 2
def baseEnd_295436 : Nat := 134845040570498967992285

theorem tailTrace_295436 : CollatzResearch.WordTrace tailWord_295436 prefixEnd_295436 134845040570498967992285 := by
  unfold tailWord_295436
  simp only [CollatzResearch.WordTrace]
  refine ⟨5387718078846651648433081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7183624105128868864577441 5387718078846651648433081)
  ·
    refine ⟨4040788559134988736324811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5387718078846651648433081 4040788559134988736324811)
    ·
      refine ⟨6061182838702483104487217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4040788559134988736324811 6061182838702483104487217)
      ·
        refine ⟨4545887129026862328365413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6061182838702483104487217 4545887129026862328365413)
        ·
          refine ⟨852353836692536686568515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4545887129026862328365413 852353836692536686568515)
          ·
            refine ⟨1278530755038805029852773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852353836692536686568515 1278530755038805029852773)
            ·
              refine ⟨239724516569775943097395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1278530755038805029852773 239724516569775943097395)
              ·
                refine ⟨359586774854663914646093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239724516569775943097395 359586774854663914646093)
                ·
                  refine ⟨134845040570498967992285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359586774854663914646093 134845040570498967992285)
                  ·
                    rfl

theorem cell20_295436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_295436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295436 prefixEnd_295436 := by exact prefixLift 295436
  have htrace : WordTrace (prefixWord ++ tailWord_295436) baseStart_295436 baseEnd_295436 := by
    simpa [prefixWord, tailWord_295436, baseEnd_295436] using wordTrace_append hprefix tailTrace_295436
  have hstable : (prefixWord ++ tailWord_295436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295436).length < 2 ^ (prefixWord ++ tailWord_295436).sum := by decide
  have hdescent : baseEnd_295436 < baseStart_295436 := by decide
  rcases family_descends (prefixWord ++ tailWord_295436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295481 : List Nat := [1, 2, 1, 5, 1, 1, 3, 4, 2]
def baseStart_295481 : Nat := 118140960795 + 295481 * 2 ^ 59
def prefixEnd_295481 : Nat := 4983230072969 + 3 ^ 40 * 295481 * 2
def baseEnd_295481 : Nat := 134865579796678811492101

theorem tailTrace_295481 : CollatzResearch.WordTrace tailWord_295481 prefixEnd_295481 134865579796678811492101 := by
  unfold tailWord_295481
  simp only [CollatzResearch.WordTrace]
  refine ⟨10777077442530275982254297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7184718295020183988169531 10777077442530275982254297)
  ·
    refine ⟨8082808081897706986690723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10777077442530275982254297 8082808081897706986690723)
    ·
      refine ⟨12124212122846560480036085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8082808081897706986690723 12124212122846560480036085)
      ·
        refine ⟨1136644886516865045003383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12124212122846560480036085 1136644886516865045003383)
        ·
          refine ⟨1704967329775297567505075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136644886516865045003383 1704967329775297567505075)
          ·
            refine ⟨2557450994662946351257613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704967329775297567505075 2557450994662946351257613)
            ·
              refine ⟨959044122998604881721605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2557450994662946351257613 959044122998604881721605)
              ·
                refine ⟨179820773062238415322801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 959044122998604881721605 179820773062238415322801)
                ·
                  refine ⟨134865579796678811492101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179820773062238415322801 134865579796678811492101)
                  ·
                    rfl

theorem cell20_295481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 2].length) (baseStart_295481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295481 prefixEnd_295481 := by exact prefixLift 295481
  have htrace : WordTrace (prefixWord ++ tailWord_295481) baseStart_295481 baseEnd_295481 := by
    simpa [prefixWord, tailWord_295481, baseEnd_295481] using wordTrace_append hprefix tailTrace_295481
  have hstable : (prefixWord ++ tailWord_295481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295481).length < 2 ^ (prefixWord ++ tailWord_295481).sum := by decide
  have hdescent : baseEnd_295481 < baseStart_295481 := by decide
  rcases family_descends (prefixWord ++ tailWord_295481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295495 : List Nat := [1, 1, 4, 1, 4, 1, 2, 3, 3]
def baseStart_295495 : Nat := 118140960795 + 295495 * 2 ^ 59
def prefixEnd_295495 : Nat := 4983230072969 + 3 ^ 40 * 295495 * 2
def baseEnd_295495 : Nat := 134871969778156985025377

theorem tailTrace_295495 : CollatzResearch.WordTrace tailWord_295495 prefixEnd_295495 134871969778156985025377 := by
  unfold tailWord_295495
  simp only [CollatzResearch.WordTrace]
  refine ⟨10777588064479556373263939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7185058709653037582175959 10777588064479556373263939)
  ·
    refine ⟨16166382096719334559895909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10777588064479556373263939 16166382096719334559895909)
    ·
      refine ⟨3031196643134875229980483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16166382096719334559895909 3031196643134875229980483)
      ·
        refine ⟨4546794964702312844970725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3031196643134875229980483 4546794964702312844970725)
        ·
          refine ⟨852524055881683658432011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4546794964702312844970725 852524055881683658432011)
          ·
            refine ⟨1278786083822525487648017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852524055881683658432011 1278786083822525487648017)
            ·
              refine ⟨959089562866894115736013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1278786083822525487648017 959089562866894115736013)
              ·
                refine ⟨359658586075085293401005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 959089562866894115736013 359658586075085293401005)
                ·
                  refine ⟨134871969778156985025377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359658586075085293401005 134871969778156985025377)
                  ·
                    rfl

theorem cell20_295495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 3].length) (baseStart_295495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295495 prefixEnd_295495 := by exact prefixLift 295495
  have htrace : WordTrace (prefixWord ++ tailWord_295495) baseStart_295495 baseEnd_295495 := by
    simpa [prefixWord, tailWord_295495, baseEnd_295495] using wordTrace_append hprefix tailTrace_295495
  have hstable : (prefixWord ++ tailWord_295495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295495).length < 2 ^ (prefixWord ++ tailWord_295495).sum := by decide
  have hdescent : baseEnd_295495 < baseStart_295495 := by decide
  rcases family_descends (prefixWord ++ tailWord_295495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295523 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 6]
def baseStart_295523 : Nat := 118140960795 + 295523 * 2 ^ 59
def prefixEnd_295523 : Nat := 4983230072969 + 3 ^ 40 * 295523 * 2
def baseEnd_295523 : Nat := 134884749741113332091929

theorem tailTrace_295523 : CollatzResearch.WordTrace tailWord_295523 prefixEnd_295523 134884749741113332091929 := by
  unfold tailWord_295523
  simp only [CollatzResearch.WordTrace]
  refine ⟨10778609308378117155283223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7185739538918744770188815 10778609308378117155283223)
  ·
    refine ⟨16167913962567175732924835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10778609308378117155283223 16167913962567175732924835)
    ·
      refine ⟨24251870943850763599387253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16167913962567175732924835 24251870943850763599387253)
      ·
        refine ⟨2273612900986009087442555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24251870943850763599387253 2273612900986009087442555)
        ·
          refine ⟨3410419351479013631163833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2273612900986009087442555 3410419351479013631163833)
          ·
            refine ⟨2557814513609260223372875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3410419351479013631163833 2557814513609260223372875)
            ·
              refine ⟨3836721770413890335059313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2557814513609260223372875 3836721770413890335059313)
              ·
                refine ⟨2877541327810417751294485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3836721770413890335059313 2877541327810417751294485)
                ·
                  refine ⟨134884749741113332091929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2877541327810417751294485 134884749741113332091929)
                  ·
                    rfl

theorem cell20_295523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_295523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295523 prefixEnd_295523 := by exact prefixLift 295523
  have htrace : WordTrace (prefixWord ++ tailWord_295523) baseStart_295523 baseEnd_295523 := by
    simpa [prefixWord, tailWord_295523, baseEnd_295523] using wordTrace_append hprefix tailTrace_295523
  have hstable : (prefixWord ++ tailWord_295523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295523).length < 2 ^ (prefixWord ++ tailWord_295523).sum := by decide
  have hdescent : baseEnd_295523 < baseStart_295523 := by decide
  rcases family_descends (prefixWord ++ tailWord_295523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295533 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 5]
def baseStart_295533 : Nat := 118140960795 + 295533 * 2 ^ 59
def prefixEnd_295533 : Nat := 4983230072969 + 3 ^ 40 * 295533 * 2
def baseEnd_295533 : Nat := 134889314013597741758555

theorem tailTrace_295533 : CollatzResearch.WordTrace tailWord_295533 prefixEnd_295533 134889314013597741758555 := by
  unfold tailWord_295533
  simp only [CollatzResearch.WordTrace]
  refine ⟨10778974038341888863147253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7185982692227925908764835 10778974038341888863147253)
  ·
    refine ⟨1010528816094552080920055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10778974038341888863147253 1010528816094552080920055)
    ·
      refine ⟨1515793224141828121380083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1010528816094552080920055 1515793224141828121380083)
      ·
        refine ⟨2273689836212742182070125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1515793224141828121380083 2273689836212742182070125)
        ·
          refine ⟨852633688579778318276297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2273689836212742182070125 852633688579778318276297)
          ·
            refine ⟨639475266434833738707223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 852633688579778318276297 639475266434833738707223)
            ·
              refine ⟨959212899652250608060835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639475266434833738707223 959212899652250608060835)
              ·
                refine ⟨1438819349478375912091253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 959212899652250608060835 1438819349478375912091253)
                ·
                  refine ⟨134889314013597741758555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1438819349478375912091253 134889314013597741758555)
                  ·
                    rfl

theorem cell20_295533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_295533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295533 prefixEnd_295533 := by exact prefixLift 295533
  have htrace : WordTrace (prefixWord ++ tailWord_295533) baseStart_295533 baseEnd_295533 := by
    simpa [prefixWord, tailWord_295533, baseEnd_295533] using wordTrace_append hprefix tailTrace_295533
  have hstable : (prefixWord ++ tailWord_295533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295533).length < 2 ^ (prefixWord ++ tailWord_295533).sum := by decide
  have hdescent : baseEnd_295533 < baseStart_295533 := by decide
  rcases family_descends (prefixWord ++ tailWord_295533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295591 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 4]
def baseStart_295591 : Nat := 118140960795 + 295591 * 2 ^ 59
def prefixEnd_295591 : Nat := 4983230072969 + 3 ^ 40 * 295591 * 2
def baseEnd_295591 : Nat := 134915786794007317824985

theorem tailTrace_295591 : CollatzResearch.WordTrace tailWord_295591 prefixEnd_295591 134915786794007317824985 := by
  unfold tailWord_295591
  simp only [CollatzResearch.WordTrace]
  refine ⟨10781089472131764768758627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7187392981421176512505751 10781089472131764768758627)
  ·
    refine ⟨16171634208197647153137941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10781089472131764768758627 16171634208197647153137941)
    ·
      refine ⟨758045353509264710303341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16171634208197647153137941 758045353509264710303341)
      ·
        refine ⟨284267007565974266363753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 758045353509264710303341 284267007565974266363753)
        ·
          refine ⟨213200255674480699772815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284267007565974266363753 213200255674480699772815)
          ·
            refine ⟨319800383511721049659223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213200255674480699772815 319800383511721049659223)
            ·
              refine ⟨479700575267581574488835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319800383511721049659223 479700575267581574488835)
              ·
                refine ⟨719550862901372361733253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479700575267581574488835 719550862901372361733253)
                ·
                  refine ⟨134915786794007317824985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 719550862901372361733253 134915786794007317824985)
                  ·
                    rfl

theorem cell20_295591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 4].length) (baseStart_295591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295591 prefixEnd_295591 := by exact prefixLift 295591
  have htrace : WordTrace (prefixWord ++ tailWord_295591) baseStart_295591 baseEnd_295591 := by
    simpa [prefixWord, tailWord_295591, baseEnd_295591] using wordTrace_append hprefix tailTrace_295591
  have hstable : (prefixWord ++ tailWord_295591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295591).length < 2 ^ (prefixWord ++ tailWord_295591).sum := by decide
  have hdescent : baseEnd_295591 < baseStart_295591 := by decide
  rcases family_descends (prefixWord ++ tailWord_295591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295605 : List Nat := [1, 3, 3, 3, 1, 3, 2, 1, 3]
def baseStart_295605 : Nat := 118140960795 + 295605 * 2 ^ 59
def prefixEnd_295605 : Nat := 4983230072969 + 3 ^ 40 * 295605 * 2
def baseEnd_295605 : Nat := 134922176775485491358261

theorem tailTrace_295605 : CollatzResearch.WordTrace tailWord_295605 prefixEnd_295605 134922176775485491358261 := by
  unfold tailWord_295605
  simp only [CollatzResearch.WordTrace]
  refine ⟨10781600094081045159768269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7187733396054030106512179 10781600094081045159768269)
  ·
    refine ⟨4043100035280391934913101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10781600094081045159768269 4043100035280391934913101)
    ·
      refine ⟨1516162513230146975592413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4043100035280391934913101 1516162513230146975592413)
      ·
        refine ⟨568560942461305115847155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1516162513230146975592413 568560942461305115847155)
        ·
          refine ⟨852841413691957673770733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568560942461305115847155 852841413691957673770733)
          ·
            refine ⟨319815530134484127664025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 852841413691957673770733 319815530134484127664025)
            ·
              refine ⟨239861647600863095748019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 319815530134484127664025 239861647600863095748019)
              ·
                refine ⟨359792471401294643622029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239861647600863095748019 359792471401294643622029)
                ·
                  refine ⟨134922176775485491358261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359792471401294643622029 134922176775485491358261)
                  ·
                    rfl

theorem cell20_295605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_295605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295605 prefixEnd_295605 := by exact prefixLift 295605
  have htrace : WordTrace (prefixWord ++ tailWord_295605) baseStart_295605 baseEnd_295605 := by
    simpa [prefixWord, tailWord_295605, baseEnd_295605] using wordTrace_append hprefix tailTrace_295605
  have hstable : (prefixWord ++ tailWord_295605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295605).length < 2 ^ (prefixWord ++ tailWord_295605).sum := by decide
  have hdescent : baseEnd_295605 < baseStart_295605 := by decide
  rcases family_descends (prefixWord ++ tailWord_295605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295647 : List Nat := [1, 1, 2, 3, 2, 4, 2, 2, 3]
def baseStart_295647 : Nat := 118140960795 + 295647 * 2 ^ 59
def prefixEnd_295647 : Nat := 4983230072969 + 3 ^ 40 * 295647 * 2
def baseEnd_295647 : Nat := 134941346719920011958089

theorem tailTrace_295647 : CollatzResearch.WordTrace tailWord_295647 prefixEnd_295647 134941346719920011958089 := by
  unfold tailWord_295647
  simp only [CollatzResearch.WordTrace]
  refine ⟨10783131959928886332797195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7188754639952590888531463 10783131959928886332797195)
  ·
    refine ⟨16174697939893329499195793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10783131959928886332797195 16174697939893329499195793)
    ·
      refine ⟨12131023454919997124396845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16174697939893329499195793 12131023454919997124396845)
      ·
        refine ⟨4549133795594998921648817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12131023454919997124396845 4549133795594998921648817)
        ·
          refine ⟨3411850346696249191236613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4549133795594998921648817 3411850346696249191236613)
          ·
            refine ⟨639721940005546723356865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3411850346696249191236613 639721940005546723356865)
            ·
              refine ⟨479791455004160042517649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 639721940005546723356865 479791455004160042517649)
              ·
                refine ⟨359843591253120031888237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479791455004160042517649 359843591253120031888237)
                ·
                  refine ⟨134941346719920011958089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359843591253120031888237 134941346719920011958089)
                  ·
                    rfl

theorem cell20_295647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 3].length) (baseStart_295647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295647 prefixEnd_295647 := by exact prefixLift 295647
  have htrace : WordTrace (prefixWord ++ tailWord_295647) baseStart_295647 baseEnd_295647 := by
    simpa [prefixWord, tailWord_295647, baseEnd_295647] using wordTrace_append hprefix tailTrace_295647
  have hstable : (prefixWord ++ tailWord_295647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295647).length < 2 ^ (prefixWord ++ tailWord_295647).sum := by decide
  have hdescent : baseEnd_295647 < baseStart_295647 := by decide
  rcases family_descends (prefixWord ++ tailWord_295647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295698 : List Nat := [3, 2, 4, 1, 3, 1, 1, 2, 3]
def baseStart_295698 : Nat := 118140960795 + 295698 * 2 ^ 59
def prefixEnd_295698 : Nat := 4983230072969 + 3 ^ 40 * 295698 * 2
def baseEnd_295698 : Nat := 134964624509590501257881

theorem tailTrace_295698 : CollatzResearch.WordTrace tailWord_295698 prefixEnd_295698 134964624509590501257881 := by
  unfold tailWord_295698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2696248020686030510725937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7189994721829414695269165 2696248020686030510725937)
  ·
    refine ⟨2022186015514522883044453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2696248020686030510725937 2022186015514522883044453)
    ·
      refine ⟨379159877908973040570835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2022186015514522883044453 379159877908973040570835)
      ·
        refine ⟨568739816863459560856253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379159877908973040570835 568739816863459560856253)
        ·
          refine ⟨213277431323797335321095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 568739816863459560856253 213277431323797335321095)
          ·
            refine ⟨319916146985696002981643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213277431323797335321095 319916146985696002981643)
            ·
              refine ⟨479874220478544004472465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319916146985696002981643 479874220478544004472465)
              ·
                refine ⟨359905665358908003354349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 479874220478544004472465 359905665358908003354349)
                ·
                  refine ⟨134964624509590501257881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 359905665358908003354349 134964624509590501257881)
                  ·
                    rfl

theorem cell20_295698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_295698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295698 prefixEnd_295698 := by exact prefixLift 295698
  have htrace : WordTrace (prefixWord ++ tailWord_295698) baseStart_295698 baseEnd_295698 := by
    simpa [prefixWord, tailWord_295698, baseEnd_295698] using wordTrace_append hprefix tailTrace_295698
  have hstable : (prefixWord ++ tailWord_295698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295698).length < 2 ^ (prefixWord ++ tailWord_295698).sum := by decide
  have hdescent : baseEnd_295698 < baseStart_295698 := by decide
  rcases family_descends (prefixWord ++ tailWord_295698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295706 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_295706 : Nat := 118140960795 + 295706 * 2 ^ 59
def prefixEnd_295706 : Nat := 4983230072969 + 3 ^ 40 * 295706 * 2
def baseEnd_295706 : Nat := 134968275927578028991181

theorem tailTrace_295706 : CollatzResearch.WordTrace tailWord_295706 prefixEnd_295706 134968275927578028991181 := by
  unfold tailWord_295706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2696320966678784852298743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7190189244476759606129981 2696320966678784852298743)
  ·
    refine ⟨4044481450018177278448115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2696320966678784852298743 4044481450018177278448115)
    ·
      refine ⟨6066722175027265917672173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4044481450018177278448115 6066722175027265917672173)
      ·
        refine ⟨2275020815635224719127065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6066722175027265917672173 2275020815635224719127065)
        ·
          refine ⟨1706265611726418539345299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2275020815635224719127065 1706265611726418539345299)
          ·
            refine ⟨2559398417589627809017949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1706265611726418539345299 2559398417589627809017949)
            ·
              refine ⟨959774406596110428381731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2559398417589627809017949 959774406596110428381731)
              ·
                refine ⟨1439661609894165642572597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 959774406596110428381731 1439661609894165642572597)
                ·
                  refine ⟨134968275927578028991181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1439661609894165642572597 134968275927578028991181)
                  ·
                    rfl

theorem cell20_295706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_295706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295706 prefixEnd_295706 := by exact prefixLift 295706
  have htrace : WordTrace (prefixWord ++ tailWord_295706) baseStart_295706 baseEnd_295706 := by
    simpa [prefixWord, tailWord_295706, baseEnd_295706] using wordTrace_append hprefix tailTrace_295706
  have hstable : (prefixWord ++ tailWord_295706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295706).length < 2 ^ (prefixWord ++ tailWord_295706).sum := by decide
  have hdescent : baseEnd_295706 < baseStart_295706 := by decide
  rcases family_descends (prefixWord ++ tailWord_295706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295727 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 9]
def baseStart_295727 : Nat := 118140960795 + 295727 * 2 ^ 59
def prefixEnd_295727 : Nat := 4983230072969 + 3 ^ 40 * 295727 * 2
def baseEnd_295727 : Nat := 134977860899795289291095

theorem tailTrace_295727 : CollatzResearch.WordTrace tailWord_295727 prefixEnd_295727 134977860899795289291095 := by
  unfold tailWord_295727
  simp only [CollatzResearch.WordTrace]
  refine ⟨10786049799639059995709435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7190699866426039997139623 10786049799639059995709435)
  ·
    refine ⟨16179074699458589993564153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10786049799639059995709435 16179074699458589993564153)
    ·
      refine ⟨12134306024593942495173115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16179074699458589993564153 12134306024593942495173115)
      ·
        refine ⟨18201459036890913742759673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12134306024593942495173115 18201459036890913742759673)
        ·
          refine ⟨13651094277668185307069755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18201459036890913742759673 13651094277668185307069755)
          ·
            refine ⟨20476641416502277960604633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13651094277668185307069755 20476641416502277960604633)
            ·
              refine ⟨15357481062376708470453475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20476641416502277960604633 15357481062376708470453475)
              ·
                refine ⟨23036221593565062705680213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15357481062376708470453475 23036221593565062705680213)
                ·
                  refine ⟨134977860899795289291095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23036221593565062705680213 134977860899795289291095)
                  ·
                    rfl

theorem cell20_295727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 9].length) (baseStart_295727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295727 prefixEnd_295727 := by exact prefixLift 295727
  have htrace : WordTrace (prefixWord ++ tailWord_295727) baseStart_295727 baseEnd_295727 := by
    simpa [prefixWord, tailWord_295727, baseEnd_295727] using wordTrace_append hprefix tailTrace_295727
  have hstable : (prefixWord ++ tailWord_295727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295727).length < 2 ^ (prefixWord ++ tailWord_295727).sum := by decide
  have hdescent : baseEnd_295727 < baseStart_295727 := by decide
  rcases family_descends (prefixWord ++ tailWord_295727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295750 : List Nat := [6, 1, 1, 2, 3, 1, 6]
def baseStart_295750 : Nat := 118140960795 + 295750 * 2 ^ 59
def prefixEnd_295750 : Nat := 4983230072969 + 3 ^ 40 * 295750 * 2
def baseEnd_295750 : Nat := 14998706525167714613815

theorem tailTrace_295750 : CollatzResearch.WordTrace tailWord_295750 prefixEnd_295750 14998706525167714613815 := by
  unfold tailWord_295750
  simp only [CollatzResearch.WordTrace]
  refine ⟨337090271204866716368647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7191259119037156615864469 337090271204866716368647)
  ·
    refine ⟨505635406807300074552971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 337090271204866716368647 505635406807300074552971)
    ·
      refine ⟨758453110210950111829457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 505635406807300074552971 758453110210950111829457)
      ·
        refine ⟨568839832658212583872093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 758453110210950111829457 568839832658212583872093)
        ·
          refine ⟨213314937246829718952035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 568839832658212583872093 213314937246829718952035)
          ·
            refine ⟨319972405870244578428053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213314937246829718952035 319972405870244578428053)
            ·
              refine ⟨14998706525167714613815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 319972405870244578428053 14998706525167714613815)
              ·
                rfl

theorem cell20_295750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 6].length) (baseStart_295750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295750 prefixEnd_295750 := by exact prefixLift 295750
  have htrace : WordTrace (prefixWord ++ tailWord_295750) baseStart_295750 baseEnd_295750 := by
    simpa [prefixWord, tailWord_295750, baseEnd_295750] using wordTrace_append hprefix tailTrace_295750
  have hstable : (prefixWord ++ tailWord_295750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295750).length < 2 ^ (prefixWord ++ tailWord_295750).sum := by decide
  have hdescent : baseEnd_295750 < baseStart_295750 := by decide
  rcases family_descends (prefixWord ++ tailWord_295750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295764 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 4]
def baseStart_295764 : Nat := 118140960795 + 295764 * 2 ^ 59
def prefixEnd_295764 : Nat := 4983230072969 + 3 ^ 40 * 295764 * 2
def baseEnd_295764 : Nat := 134994748707987605057611

theorem tailTrace_295764 : CollatzResearch.WordTrace tailWord_295764 prefixEnd_295764 134994748707987605057611 := by
  unfold tailWord_295764
  simp only [CollatzResearch.WordTrace]
  refine ⟨5393699650252507657403173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7191599533670010209870897 5393699650252507657403173)
  ·
    refine ⟨1011318684422345185763095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5393699650252507657403173 1011318684422345185763095)
    ·
      refine ⟨1516978026633517778644643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1011318684422345185763095 1516978026633517778644643)
      ·
        refine ⟨2275467039950276667966965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1516978026633517778644643 2275467039950276667966965)
        ·
          refine ⟨213325034995338437621903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2275467039950276667966965 213325034995338437621903)
          ·
            refine ⟨319987552493007656432855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213325034995338437621903 319987552493007656432855)
            ·
              refine ⟨479981328739511484649283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319987552493007656432855 479981328739511484649283)
              ·
                refine ⟨719971993109267226973925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 479981328739511484649283 719971993109267226973925)
                ·
                  refine ⟨134994748707987605057611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 719971993109267226973925 134994748707987605057611)
                  ·
                    rfl

theorem cell20_295764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_295764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295764 prefixEnd_295764 := by exact prefixLift 295764
  have htrace : WordTrace (prefixWord ++ tailWord_295764) baseStart_295764 baseEnd_295764 := by
    simpa [prefixWord, tailWord_295764, baseEnd_295764] using wordTrace_append hprefix tailTrace_295764
  have hstable : (prefixWord ++ tailWord_295764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295764).length < 2 ^ (prefixWord ++ tailWord_295764).sum := by decide
  have hdescent : baseEnd_295764 < baseStart_295764 := by decide
  rcases family_descends (prefixWord ++ tailWord_295764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295768 : List Nat := [2, 1, 2, 2, 1, 1, 1, 8, 2]
def baseStart_295768 : Nat := 118140960795 + 295768 * 2 ^ 59
def prefixEnd_295768 : Nat := 4983230072969 + 3 ^ 40 * 295768 * 2
def baseEnd_295768 : Nat := 134996574416981368924261

theorem tailTrace_295768 : CollatzResearch.WordTrace tailWord_295768 prefixEnd_295768 134996574416981368924261 := by
  unfold tailWord_295768
  simp only [CollatzResearch.WordTrace]
  refine ⟨5393772596245261998975979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7191696794993682665301305 5393772596245261998975979)
  ·
    refine ⟨8090658894367892998463969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5393772596245261998975979 8090658894367892998463969)
    ·
      refine ⟨6067994170775919748847977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8090658894367892998463969 6067994170775919748847977)
      ·
        refine ⟨4550995628081939811635983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6067994170775919748847977 4550995628081939811635983)
        ·
          refine ⟨6826493442122909717453975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4550995628081939811635983 6826493442122909717453975)
          ·
            refine ⟨10239740163184364576180963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6826493442122909717453975 10239740163184364576180963)
            ·
              refine ⟨15359610244776546864271445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10239740163184364576180963 15359610244776546864271445)
              ·
                refine ⟨179995432555975158565681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 15359610244776546864271445 179995432555975158565681)
                ·
                  refine ⟨134996574416981368924261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179995432555975158565681 134996574416981368924261)
                  ·
                    rfl

theorem cell20_295768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 2].length) (baseStart_295768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295768 prefixEnd_295768 := by exact prefixLift 295768
  have htrace : WordTrace (prefixWord ++ tailWord_295768) baseStart_295768 baseEnd_295768 := by
    simpa [prefixWord, tailWord_295768, baseEnd_295768] using wordTrace_append hprefix tailTrace_295768
  have hstable : (prefixWord ++ tailWord_295768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295768).length < 2 ^ (prefixWord ++ tailWord_295768).sum := by decide
  have hdescent : baseEnd_295768 < baseStart_295768 := by decide
  rcases family_descends (prefixWord ++ tailWord_295768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295778 : List Nat := [3, 3, 2, 1, 3, 1, 1, 3, 3]
def baseStart_295778 : Nat := 118140960795 + 295778 * 2 ^ 59
def prefixEnd_295778 : Nat := 4983230072969 + 3 ^ 40 * 295778 * 2
def baseEnd_295778 : Nat := 135001138689465778590887

theorem tailTrace_295778 : CollatzResearch.WordTrace tailWord_295778 prefixEnd_295778 135001138689465778590887 := by
  unfold tailWord_295778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2696977480613573926453997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7191939948302863803877325 2696977480613573926453997)
  ·
    refine ⟨1011366555230090222420249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2696977480613573926453997 1011366555230090222420249)
    ·
      refine ⟨758524916422567666815187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1011366555230090222420249 758524916422567666815187)
      ·
        refine ⟨1137787374633851500222781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 758524916422567666815187 1137787374633851500222781)
        ·
          refine ⟨426670265487694312583543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1137787374633851500222781 426670265487694312583543)
          ·
            refine ⟨640005398231541468875315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426670265487694312583543 640005398231541468875315)
            ·
              refine ⟨960008097347312203312973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640005398231541468875315 960008097347312203312973)
              ·
                refine ⟨360003036505242076242365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 960008097347312203312973 360003036505242076242365)
                ·
                  refine ⟨135001138689465778590887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360003036505242076242365 135001138689465778590887)
                  ·
                    rfl

theorem cell20_295778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_295778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295778 prefixEnd_295778 := by exact prefixLift 295778
  have htrace : WordTrace (prefixWord ++ tailWord_295778) baseStart_295778 baseEnd_295778 := by
    simpa [prefixWord, tailWord_295778, baseEnd_295778] using wordTrace_append hprefix tailTrace_295778
  have hstable : (prefixWord ++ tailWord_295778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295778).length < 2 ^ (prefixWord ++ tailWord_295778).sum := by decide
  have hdescent : baseEnd_295778 < baseStart_295778 := by decide
  rcases family_descends (prefixWord ++ tailWord_295778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295789 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 6]
def baseStart_295789 : Nat := 118140960795 + 295789 * 2 ^ 59
def prefixEnd_295789 : Nat := 4983230072969 + 3 ^ 40 * 295789 * 2
def baseEnd_295789 : Nat := 135006159389198629224175

theorem tailTrace_295789 : CollatzResearch.WordTrace tailWord_295789 prefixEnd_295789 135006159389198629224175 := by
  unfold tailWord_295789
  simp only [CollatzResearch.WordTrace]
  refine ⟨10788311125414444584466421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7192207416942963056310947 10788311125414444584466421)
  ·
    refine ⟨1011404168007604179793727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10788311125414444584466421 1011404168007604179793727)
    ·
      refine ⟨1517106252011406269690591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1011404168007604179793727 1517106252011406269690591)
      ·
        refine ⟨2275659378017109404535887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1517106252011406269690591 2275659378017109404535887)
        ·
          refine ⟨3413489067025664106803831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2275659378017109404535887 3413489067025664106803831)
          ·
            refine ⟨5120233600538496160205747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3413489067025664106803831 5120233600538496160205747)
            ·
              refine ⟨7680350400807744240308621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5120233600538496160205747 7680350400807744240308621)
              ·
                refine ⟨2880131400302904090115733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7680350400807744240308621 2880131400302904090115733)
                ·
                  refine ⟨135006159389198629224175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2880131400302904090115733 135006159389198629224175)
                  ·
                    rfl

theorem cell20_295789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_295789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295789 prefixEnd_295789 := by exact prefixLift 295789
  have htrace : WordTrace (prefixWord ++ tailWord_295789) baseStart_295789 baseEnd_295789 := by
    simpa [prefixWord, tailWord_295789, baseEnd_295789] using wordTrace_append hprefix tailTrace_295789
  have hstable : (prefixWord ++ tailWord_295789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295789).length < 2 ^ (prefixWord ++ tailWord_295789).sum := by decide
  have hdescent : baseEnd_295789 < baseStart_295789 := by decide
  rcases family_descends (prefixWord ++ tailWord_295789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295803 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 7]
def baseStart_295803 : Nat := 118140960795 + 295803 * 2 ^ 59
def prefixEnd_295803 : Nat := 4983230072969 + 3 ^ 40 * 295803 * 2
def baseEnd_295803 : Nat := 135012549370676802757451

theorem tailTrace_295803 : CollatzResearch.WordTrace tailWord_295803 prefixEnd_295803 135012549370676802757451 := by
  unfold tailWord_295803
  simp only [CollatzResearch.WordTrace]
  refine ⟨10788821747363724975476063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7192547831575816650317375 10788821747363724975476063)
  ·
    refine ⟨16183232621045587463214095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10788821747363724975476063 16183232621045587463214095)
    ·
      refine ⟨24274848931568381194821143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16183232621045587463214095 24274848931568381194821143)
      ·
        refine ⟨36412273397352571792231715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24274848931568381194821143 36412273397352571792231715)
        ·
          refine ⟨54618410096028857688347573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36412273397352571792231715 54618410096028857688347573)
          ·
            refine ⟨5120475946502705408282585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54618410096028857688347573 5120475946502705408282585)
            ·
              refine ⟨3840356959877029056211939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5120475946502705408282585 3840356959877029056211939)
              ·
                refine ⟨5760535439815543584317909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3840356959877029056211939 5760535439815543584317909)
                ·
                  refine ⟨135012549370676802757451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5760535439815543584317909 135012549370676802757451)
                  ·
                    rfl

theorem cell20_295803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_295803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295803 prefixEnd_295803 := by exact prefixLift 295803
  have htrace : WordTrace (prefixWord ++ tailWord_295803) baseStart_295803 baseEnd_295803 := by
    simpa [prefixWord, tailWord_295803, baseEnd_295803] using wordTrace_append hprefix tailTrace_295803
  have hstable : (prefixWord ++ tailWord_295803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295803).length < 2 ^ (prefixWord ++ tailWord_295803).sum := by decide
  have hdescent : baseEnd_295803 < baseStart_295803 := by decide
  rcases family_descends (prefixWord ++ tailWord_295803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295820 : List Nat := [2, 2, 1, 2, 1, 2, 3, 4, 3]
def baseStart_295820 : Nat := 118140960795 + 295820 * 2 ^ 59
def prefixEnd_295820 : Nat := 4983230072969 + 3 ^ 40 * 295820 * 2
def baseEnd_295820 : Nat := 135020308633900299190715

theorem tailTrace_295820 : CollatzResearch.WordTrace tailWord_295820 prefixEnd_295820 135020308633900299190715 := by
  unfold tailWord_295820
  simp only [CollatzResearch.WordTrace]
  refine ⟨5394720894151068439422457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7192961192201424585896609 5394720894151068439422457)
  ·
    refine ⟨4046040670613301329566843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5394720894151068439422457 4046040670613301329566843)
    ·
      refine ⟨6069061005919951994350265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4046040670613301329566843 6069061005919951994350265)
      ·
        refine ⟨4551795754439963995762699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6069061005919951994350265 4551795754439963995762699)
        ·
          refine ⟨6827693631659945993644049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4551795754439963995762699 6827693631659945993644049)
          ·
            refine ⟨5120770223744959495233037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6827693631659945993644049 5120770223744959495233037)
            ·
              refine ⟨1920288833904359810712389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5120770223744959495233037 1920288833904359810712389)
              ·
                refine ⟨360054156357067464508573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1920288833904359810712389 360054156357067464508573)
                ·
                  refine ⟨135020308633900299190715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360054156357067464508573 135020308633900299190715)
                  ·
                    rfl

theorem cell20_295820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_295820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295820 prefixEnd_295820 := by exact prefixLift 295820
  have htrace : WordTrace (prefixWord ++ tailWord_295820) baseStart_295820 baseEnd_295820 := by
    simpa [prefixWord, tailWord_295820, baseEnd_295820] using wordTrace_append hprefix tailTrace_295820
  have hstable : (prefixWord ++ tailWord_295820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295820).length < 2 ^ (prefixWord ++ tailWord_295820).sum := by decide
  have hdescent : baseEnd_295820 < baseStart_295820 := by decide
  rcases family_descends (prefixWord ++ tailWord_295820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295861 : List Nat := [1, 3, 3, 2, 1, 1, 4, 3, 2]
def baseStart_295861 : Nat := 118140960795 + 295861 * 2 ^ 59
def prefixEnd_295861 : Nat := 4983230072969 + 3 ^ 40 * 295861 * 2
def baseEnd_295861 : Nat := 135039022151086378823881

theorem tailTrace_295861 : CollatzResearch.WordTrace tailWord_295861 prefixEnd_295861 135039022151086378823881 := by
  unfold tailWord_295861
  simp only [CollatzResearch.WordTrace]
  refine ⟨10790937181153600881087437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7193958120769067254058291 10790937181153600881087437)
  ·
    refine ⟨4046601442932600330407789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10790937181153600881087437 4046601442932600330407789)
    ·
      refine ⟨1517475541099725123902921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4046601442932600330407789 1517475541099725123902921)
      ·
        refine ⟨1138106655824793842927191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1517475541099725123902921 1138106655824793842927191)
        ·
          refine ⟨1707159983737190764390787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1138106655824793842927191 1707159983737190764390787)
          ·
            refine ⟨2560739975605786146586181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707159983737190764390787 2560739975605786146586181)
            ·
              refine ⟨480138745426084902484909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2560739975605786146586181 480138745426084902484909)
              ·
                refine ⟨180052029534781838431841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 480138745426084902484909 180052029534781838431841)
                ·
                  refine ⟨135039022151086378823881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180052029534781838431841 135039022151086378823881)
                  ·
                    rfl

theorem cell20_295861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_295861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295861 prefixEnd_295861 := by exact prefixLift 295861
  have htrace : WordTrace (prefixWord ++ tailWord_295861) baseStart_295861 baseEnd_295861 := by
    simpa [prefixWord, tailWord_295861, baseEnd_295861] using wordTrace_append hprefix tailTrace_295861
  have hstable : (prefixWord ++ tailWord_295861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295861).length < 2 ^ (prefixWord ++ tailWord_295861).sum := by decide
  have hdescent : baseEnd_295861 < baseStart_295861 := by decide
  rcases family_descends (prefixWord ++ tailWord_295861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295872 : List Nat := [2, 1, 1, 2, 3, 4, 7]
def baseStart_295872 : Nat := 118140960795 + 295872 * 2 ^ 59
def prefixEnd_295872 : Nat := 4983230072969 + 3 ^ 40 * 295872 * 2
def baseEnd_295872 : Nat := 15004893650091025495241

theorem tailTrace_295872 : CollatzResearch.WordTrace tailWord_295872 prefixEnd_295872 15004893650091025495241 := by
  unfold tailWord_295872
  simp only [CollatzResearch.WordTrace]
  refine ⟨5395669192056874879868935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7194225589409166506491913 5395669192056874879868935)
  ·
    refine ⟨8093503788085312319803403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5395669192056874879868935 8093503788085312319803403)
    ·
      refine ⟨12140255682127968479705105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8093503788085312319803403 12140255682127968479705105)
      ·
        refine ⟨9105191761595976359778829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12140255682127968479705105 9105191761595976359778829)
        ·
          refine ⟨3414446910598491134917061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9105191761595976359778829 3414446910598491134917061)
          ·
            refine ⟨640208795737217087796949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3414446910598491134917061 640208795737217087796949)
            ·
              refine ⟨15004893650091025495241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 640208795737217087796949 15004893650091025495241)
              ·
                rfl

theorem cell20_295872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 7].length) (baseStart_295872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295872 prefixEnd_295872 := by exact prefixLift 295872
  have htrace : WordTrace (prefixWord ++ tailWord_295872) baseStart_295872 baseEnd_295872 := by
    simpa [prefixWord, tailWord_295872, baseEnd_295872] using wordTrace_append hprefix tailTrace_295872
  have hstable : (prefixWord ++ tailWord_295872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295872).length < 2 ^ (prefixWord ++ tailWord_295872).sum := by decide
  have hdescent : baseEnd_295872 < baseStart_295872 := by decide
  rcases family_descends (prefixWord ++ tailWord_295872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295892 : List Nat := [2, 4, 1, 2, 1, 3, 3, 1, 3]
def baseStart_295892 : Nat := 118140960795 + 295892 * 2 ^ 59
def prefixEnd_295892 : Nat := 4983230072969 + 3 ^ 40 * 295892 * 2
def baseEnd_295892 : Nat := 135053171395788048790421

theorem tailTrace_295892 : CollatzResearch.WordTrace tailWord_295892 prefixEnd_295892 135053171395788048790421 := by
  unfold tailWord_295892
  simp only [CollatzResearch.WordTrace]
  refine ⟨5396033922020646587732965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7194711896027528783643953 5396033922020646587732965)
  ·
    refine ⟨1011756360378871235199931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5396033922020646587732965 1011756360378871235199931)
    ·
      refine ⟨1517634540568306852799897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1011756360378871235199931 1517634540568306852799897)
      ·
        refine ⟨1138225905426230139599923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1517634540568306852799897 1138225905426230139599923)
        ·
          refine ⟨1707338858139345209399885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1138225905426230139599923 1707338858139345209399885)
          ·
            refine ⟨640252071802254453524957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1707338858139345209399885 640252071802254453524957)
            ·
              refine ⟨240094526925845420071859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 640252071802254453524957 240094526925845420071859)
              ·
                refine ⟨360141790388768130107789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240094526925845420071859 360141790388768130107789)
                ·
                  refine ⟨135053171395788048790421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360141790388768130107789 135053171395788048790421)
                  ·
                    rfl

theorem cell20_295892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_295892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295892 prefixEnd_295892 := by exact prefixLift 295892
  have htrace : WordTrace (prefixWord ++ tailWord_295892) baseStart_295892 baseEnd_295892 := by
    simpa [prefixWord, tailWord_295892, baseEnd_295892] using wordTrace_append hprefix tailTrace_295892
  have hstable : (prefixWord ++ tailWord_295892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295892).length < 2 ^ (prefixWord ++ tailWord_295892).sum := by decide
  have hdescent : baseEnd_295892 < baseStart_295892 := by decide
  rcases family_descends (prefixWord ++ tailWord_295892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295906 : List Nat := [3, 3, 3, 1, 1, 2, 1, 6]
def baseStart_295906 : Nat := 118140960795 + 295906 * 2 ^ 59
def prefixEnd_295906 : Nat := 4983230072969 + 3 ^ 40 * 295906 * 2
def baseEnd_295906 : Nat := 45019853792422074107899

theorem tailTrace_295906 : CollatzResearch.WordTrace tailWord_295906 prefixEnd_295906 45019853792422074107899 := by
  unfold tailWord_295906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2698144616497643391618893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7195052310660382377650381 2698144616497643391618893)
  ·
    refine ⟨1011804231186616271857085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2698144616497643391618893 1011804231186616271857085)
    ·
      refine ⟨379426586694981101946407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1011804231186616271857085 379426586694981101946407)
      ·
        refine ⟨569139880042471652919611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379426586694981101946407 569139880042471652919611)
        ·
          refine ⟨853709820063707479379417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569139880042471652919611 853709820063707479379417)
          ·
            refine ⟨640282365047780609534563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 853709820063707479379417 640282365047780609534563)
            ·
              refine ⟨960423547571670914301845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640282365047780609534563 960423547571670914301845)
              ·
                refine ⟨45019853792422074107899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 960423547571670914301845 45019853792422074107899)
                ·
                  rfl

theorem cell20_295906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_295906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295906 prefixEnd_295906 := by exact prefixLift 295906
  have htrace : WordTrace (prefixWord ++ tailWord_295906) baseStart_295906 baseEnd_295906 := by
    simpa [prefixWord, tailWord_295906, baseEnd_295906] using wordTrace_append hprefix tailTrace_295906
  have hstable : (prefixWord ++ tailWord_295906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295906).length < 2 ^ (prefixWord ++ tailWord_295906).sum := by decide
  have hdescent : baseEnd_295906 < baseStart_295906 := by decide
  rcases family_descends (prefixWord ++ tailWord_295906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295948 : List Nat := [2, 2, 1, 2, 3, 2, 1, 7]
def baseStart_295948 : Nat := 118140960795 + 295948 * 2 ^ 59
def prefixEnd_295948 : Nat := 4983230072969 + 3 ^ 40 * 295948 * 2
def baseEnd_295948 : Nat := 45026243773900247641175

theorem tailTrace_295948 : CollatzResearch.WordTrace tailWord_295948 prefixEnd_295948 45026243773900247641175 := by
  unfold tailWord_295948
  simp only [CollatzResearch.WordTrace]
  refine ⟨5397055165919207369752249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7196073554558943159669665 5397055165919207369752249)
  ·
    refine ⟨4047791374439405527314187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5397055165919207369752249 4047791374439405527314187)
    ·
      refine ⟨6071687061659108290971281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4047791374439405527314187 6071687061659108290971281)
      ·
        refine ⟨4553765296244331218228461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6071687061659108290971281 4553765296244331218228461)
        ·
          refine ⟨1707661986091624206835673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4553765296244331218228461 1707661986091624206835673)
          ·
            refine ⟨1280746489568718155126755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1707661986091624206835673 1280746489568718155126755)
            ·
              refine ⟨1921119734353077232690133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280746489568718155126755 1921119734353077232690133)
              ·
                refine ⟨45026243773900247641175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1921119734353077232690133 45026243773900247641175)
                ·
                  rfl

theorem cell20_295948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_295948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295948 prefixEnd_295948 := by exact prefixLift 295948
  have htrace : WordTrace (prefixWord ++ tailWord_295948) baseStart_295948 baseEnd_295948 := by
    simpa [prefixWord, tailWord_295948, baseEnd_295948] using wordTrace_append hprefix tailTrace_295948
  have hstable : (prefixWord ++ tailWord_295948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295948).length < 2 ^ (prefixWord ++ tailWord_295948).sum := by decide
  have hdescent : baseEnd_295948 < baseStart_295948 := by decide
  rcases family_descends (prefixWord ++ tailWord_295948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295992 : List Nat := [2, 1, 2, 1, 5, 3, 2, 2, 2]
def baseStart_295992 : Nat := 118140960795 + 295992 * 2 ^ 59
def prefixEnd_295992 : Nat := 4983230072969 + 3 ^ 40 * 295992 * 2
def baseEnd_295992 : Nat := 135098814120632145456679

theorem tailTrace_295992 : CollatzResearch.WordTrace tailWord_295992 prefixEnd_295992 135098814120632145456679 := by
  unfold tailWord_295992
  simp only [CollatzResearch.WordTrace]
  refine ⟨5397857571839505127053115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7197143429119340169404153 5397857571839505127053115)
  ·
    refine ⟨8096786357759257690579673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5397857571839505127053115 8096786357759257690579673)
    ·
      refine ⟨6072589768319443267934755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8096786357759257690579673 6072589768319443267934755)
      ·
        refine ⟨9108884652479164901902133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6072589768319443267934755 9108884652479164901902133)
        ·
          refine ⟨853957936169921709553325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9108884652479164901902133 853957936169921709553325)
          ·
            refine ⟨320234226063720641082497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 853957936169921709553325 320234226063720641082497)
            ·
              refine ⟨240175669547790480811873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320234226063720641082497 240175669547790480811873)
              ·
                refine ⟨180131752160842860608905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240175669547790480811873 180131752160842860608905)
                ·
                  refine ⟨135098814120632145456679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180131752160842860608905 135098814120632145456679)
                  ·
                    rfl

theorem cell20_295992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 2].length) (baseStart_295992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_295992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_295992 prefixEnd_295992 := by exact prefixLift 295992
  have htrace : WordTrace (prefixWord ++ tailWord_295992) baseStart_295992 baseEnd_295992 := by
    simpa [prefixWord, tailWord_295992, baseEnd_295992] using wordTrace_append hprefix tailTrace_295992
  have hstable : (prefixWord ++ tailWord_295992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295992).length < 2 ^ (prefixWord ++ tailWord_295992).sum := by decide
  have hdescent : baseEnd_295992 < baseStart_295992 := by decide
  rcases family_descends (prefixWord ++ tailWord_295992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296006 : List Nat := [6, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_296006 : Nat := 118140960795 + 296006 * 2 ^ 59
def prefixEnd_296006 : Nat := 4983230072969 + 3 ^ 40 * 296006 * 2
def baseEnd_296006 : Nat := 135105204102110318989955

theorem tailTrace_296006 : CollatzResearch.WordTrace tailWord_296006 prefixEnd_296006 135105204102110318989955 := by
  unfold tailWord_296006
  simp only [CollatzResearch.WordTrace]
  refine ⟨337382055175884082659871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7197483843752193763410581 337382055175884082659871)
  ·
    refine ⟨506073082763826123989807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 337382055175884082659871 506073082763826123989807)
    ·
      refine ⟨759109624145739185984711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 506073082763826123989807 759109624145739185984711)
      ·
        refine ⟨1138664436218608778977067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 759109624145739185984711 1138664436218608778977067)
        ·
          refine ⟨1707996654327913168465601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1138664436218608778977067 1707996654327913168465601)
          ·
            refine ⟨1280997490745934876349201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1707996654327913168465601 1280997490745934876349201)
            ·
              refine ⟨960748118059451157261901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1280997490745934876349201 960748118059451157261901)
              ·
                refine ⟨360280544272294183973213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 960748118059451157261901 360280544272294183973213)
                ·
                  refine ⟨135105204102110318989955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360280544272294183973213 135105204102110318989955)
                  ·
                    rfl

theorem cell20_296006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_296006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296006 prefixEnd_296006 := by exact prefixLift 296006
  have htrace : WordTrace (prefixWord ++ tailWord_296006) baseStart_296006 baseEnd_296006 := by
    simpa [prefixWord, tailWord_296006, baseEnd_296006] using wordTrace_append hprefix tailTrace_296006
  have hstable : (prefixWord ++ tailWord_296006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296006).length < 2 ^ (prefixWord ++ tailWord_296006).sum := by decide
  have hdescent : baseEnd_296006 < baseStart_296006 := by decide
  rcases family_descends (prefixWord ++ tailWord_296006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296010 : List Nat := [3, 1, 2, 1, 1, 2, 4, 3, 3]
def baseStart_296010 : Nat := 118140960795 + 296010 * 2 ^ 59
def prefixEnd_296010 : Nat := 4983230072969 + 3 ^ 40 * 296010 * 2
def baseEnd_296010 : Nat := 135107029811104082856605

theorem tailTrace_296010 : CollatzResearch.WordTrace tailWord_296010 prefixEnd_296010 135107029811104082856605 := by
  unfold tailWord_296010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699092914403449832065371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7197581105075866218840989 2699092914403449832065371)
  ·
    refine ⟨4048639371605174748098057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2699092914403449832065371 4048639371605174748098057)
    ·
      refine ⟨3036479528703881061073543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4048639371605174748098057 3036479528703881061073543)
      ·
        refine ⟨4554719293055821591610315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3036479528703881061073543 4554719293055821591610315)
        ·
          refine ⟨6832078939583732387415473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4554719293055821591610315 6832078939583732387415473)
          ·
            refine ⟨5124059204687799290561605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6832078939583732387415473 5124059204687799290561605)
            ·
              refine ⟨960761100878962366980301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5124059204687799290561605 960761100878962366980301)
              ·
                refine ⟨360285412829610887617613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 960761100878962366980301 360285412829610887617613)
                ·
                  refine ⟨135107029811104082856605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360285412829610887617613 135107029811104082856605)
                  ·
                    rfl

theorem cell20_296010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_296010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296010 prefixEnd_296010 := by exact prefixLift 296010
  have htrace : WordTrace (prefixWord ++ tailWord_296010) baseStart_296010 baseEnd_296010 := by
    simpa [prefixWord, tailWord_296010, baseEnd_296010] using wordTrace_append hprefix tailTrace_296010
  have hstable : (prefixWord ++ tailWord_296010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296010).length < 2 ^ (prefixWord ++ tailWord_296010).sum := by decide
  have hdescent : baseEnd_296010 < baseStart_296010 := by decide
  rcases family_descends (prefixWord ++ tailWord_296010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296031 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 5]
def baseStart_296031 : Nat := 118140960795 + 296031 * 2 ^ 59
def prefixEnd_296031 : Nat := 4983230072969 + 3 ^ 40 * 296031 * 2
def baseEnd_296031 : Nat := 135116614783321343156519

theorem tailTrace_296031 : CollatzResearch.WordTrace tailWord_296031 prefixEnd_296031 135116614783321343156519 := by
  unfold tailWord_296031
  simp only [CollatzResearch.WordTrace]
  refine ⟨10797137590537719914775947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7198091727025146609850631 10797137590537719914775947)
  ·
    refine ⟨16195706385806579872163921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10797137590537719914775947 16195706385806579872163921)
    ·
      refine ⟨12146779789354934904122941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16195706385806579872163921 12146779789354934904122941)
      ·
        refine ⟨4555042421008100589046103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12146779789354934904122941 4555042421008100589046103)
        ·
          refine ⟨6832563631512150883569155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4555042421008100589046103 6832563631512150883569155)
          ·
            refine ⟨10248845447268226325353733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6832563631512150883569155 10248845447268226325353733)
            ·
              refine ⟨1921658521362792436003825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10248845447268226325353733 1921658521362792436003825)
              ·
                refine ⟨1441243891022094327002869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1921658521362792436003825 1441243891022094327002869)
                ·
                  refine ⟨135116614783321343156519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1441243891022094327002869 135116614783321343156519)
                  ·
                    rfl

theorem cell20_296031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_296031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296031 prefixEnd_296031 := by exact prefixLift 296031
  have htrace : WordTrace (prefixWord ++ tailWord_296031) baseStart_296031 baseEnd_296031 := by
    simpa [prefixWord, tailWord_296031, baseEnd_296031] using wordTrace_append hprefix tailTrace_296031
  have hstable : (prefixWord ++ tailWord_296031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296031).length < 2 ^ (prefixWord ++ tailWord_296031).sum := by decide
  have hdescent : baseEnd_296031 < baseStart_296031 := by decide
  rcases family_descends (prefixWord ++ tailWord_296031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296055 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 4]
def baseStart_296055 : Nat := 118140960795 + 296055 * 2 ^ 59
def prefixEnd_296055 : Nat := 4983230072969 + 3 ^ 40 * 296055 * 2
def baseEnd_296055 : Nat := 135127569037283926356421

theorem tailTrace_296055 : CollatzResearch.WordTrace tailWord_296055 prefixEnd_296055 135127569037283926356421 := by
  unfold tailWord_296055
  simp only [CollatzResearch.WordTrace]
  refine ⟨10798012942450772013649619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7198675294967181342433079 10798012942450772013649619)
  ·
    refine ⟨16197019413676158020474429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10798012942450772013649619 16197019413676158020474429)
    ·
      refine ⟨6073882280128559257677911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16197019413676158020474429 6073882280128559257677911)
      ·
        refine ⟨9110823420192838886516867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6073882280128559257677911 9110823420192838886516867)
        ·
          refine ⟨13666235130289258329775301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9110823420192838886516867 13666235130289258329775301)
          ·
            refine ⟨2562419086929235936832869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13666235130289258329775301 2562419086929235936832869)
            ·
              refine ⟨480453578799231738156163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2562419086929235936832869 480453578799231738156163)
              ·
                refine ⟨720680368198847607234245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480453578799231738156163 720680368198847607234245)
                ·
                  refine ⟨135127569037283926356421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 720680368198847607234245 135127569037283926356421)
                  ·
                    rfl

theorem cell20_296055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_296055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296055 prefixEnd_296055 := by exact prefixLift 296055
  have htrace : WordTrace (prefixWord ++ tailWord_296055) baseStart_296055 baseEnd_296055 := by
    simpa [prefixWord, tailWord_296055, baseEnd_296055] using wordTrace_append hprefix tailTrace_296055
  have hstable : (prefixWord ++ tailWord_296055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296055).length < 2 ^ (prefixWord ++ tailWord_296055).sum := by decide
  have hdescent : baseEnd_296055 < baseStart_296055 := by decide
  rcases family_descends (prefixWord ++ tailWord_296055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296100 : List Nat := [2, 3, 1, 2, 3, 1, 8]
def baseStart_296100 : Nat := 118140960795 + 296100 * 2 ^ 59
def prefixEnd_296100 : Nat := 4983230072969 + 3 ^ 40 * 296100 * 2
def baseEnd_296100 : Nat := 15016456473718196650693

theorem tailTrace_296100 : CollatzResearch.WordTrace tailWord_296100 prefixEnd_296100 15016456473718196650693 := by
  unfold tailWord_296100
  simp only [CollatzResearch.WordTrace]
  refine ⟨5399827113643872349518877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7199769484858496466025169 5399827113643872349518877)
  ·
    refine ⟨2024935167616452131069579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5399827113643872349518877 2024935167616452131069579)
    ·
      refine ⟨3037402751424678196604369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2024935167616452131069579 3037402751424678196604369)
      ·
        refine ⟨2278052063568508647453277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3037402751424678196604369 2278052063568508647453277)
        ·
          refine ⟨854269523838190742794979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2278052063568508647453277 854269523838190742794979)
          ·
            refine ⟨1281404285757286114192469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854269523838190742794979 1281404285757286114192469)
            ·
              refine ⟨15016456473718196650693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1281404285757286114192469 15016456473718196650693)
              ·
                rfl

theorem cell20_296100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 8].length) (baseStart_296100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296100 prefixEnd_296100 := by exact prefixLift 296100
  have htrace : WordTrace (prefixWord ++ tailWord_296100) baseStart_296100 baseEnd_296100 := by
    simpa [prefixWord, tailWord_296100, baseEnd_296100] using wordTrace_append hprefix tailTrace_296100
  have hstable : (prefixWord ++ tailWord_296100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296100).length < 2 ^ (prefixWord ++ tailWord_296100).sum := by decide
  have hdescent : baseEnd_296100 < baseStart_296100 := by decide
  rcases family_descends (prefixWord ++ tailWord_296100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296138 : List Nat := [3, 1, 2, 1, 3, 2, 2, 6]
def baseStart_296138 : Nat := 118140960795 + 296138 * 2 ^ 59
def prefixEnd_296138 : Nat := 4983230072969 + 3 ^ 40 * 296138 * 2
def baseEnd_296138 : Nat := 45055150832968175529805

theorem tailTrace_296138 : CollatzResearch.WordTrace tailWord_296138 prefixEnd_296138 45055150832968175529805 := by
  unfold tailWord_296138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2700260050287519297230267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7200693467433384792614045 2700260050287519297230267)
  ·
    refine ⟨4050390075431278945845401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2700260050287519297230267 4050390075431278945845401)
    ·
      refine ⟨3037792556573459209384051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4050390075431278945845401 3037792556573459209384051)
      ·
        refine ⟨4556688834860188814076077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3037792556573459209384051 4556688834860188814076077)
        ·
          refine ⟨1708758313072570805278529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4556688834860188814076077 1708758313072570805278529)
          ·
            refine ⟨1281568734804428103958897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1708758313072570805278529 1281568734804428103958897)
            ·
              refine ⟨961176551103321077969173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1281568734804428103958897 961176551103321077969173)
              ·
                refine ⟨45055150832968175529805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 961176551103321077969173 45055150832968175529805)
                ·
                  rfl

theorem cell20_296138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_296138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296138 prefixEnd_296138 := by exact prefixLift 296138
  have htrace : WordTrace (prefixWord ++ tailWord_296138) baseStart_296138 baseEnd_296138 := by
    simpa [prefixWord, tailWord_296138, baseEnd_296138] using wordTrace_append hprefix tailTrace_296138
  have hstable : (prefixWord ++ tailWord_296138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296138).length < 2 ^ (prefixWord ++ tailWord_296138).sum := by decide
  have hdescent : baseEnd_296138 < baseStart_296138 := by decide
  rcases family_descends (prefixWord ++ tailWord_296138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296165 : List Nat := [1, 3, 1, 4, 3, 1, 1, 4, 2]
def baseStart_296165 : Nat := 118140960795 + 296165 * 2 ^ 59
def prefixEnd_296165 : Nat := 4983230072969 + 3 ^ 40 * 296165 * 2
def baseEnd_296165 : Nat := 135177776034612432689305

theorem tailTrace_296165 : CollatzResearch.WordTrace tailWord_296165 prefixEnd_296165 135177776034612432689305 := by
  unfold tailWord_296165
  simp only [CollatzResearch.WordTrace]
  refine ⟨10802024972052260800153949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7201349981368173866769299 10802024972052260800153949)
  ·
    refine ⟨4050759364519597800057731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10802024972052260800153949 4050759364519597800057731)
    ·
      refine ⟨6076139046779396700086597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4050759364519597800057731 6076139046779396700086597)
      ·
        refine ⟨1139276071271136881266237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6076139046779396700086597 1139276071271136881266237)
        ·
          refine ⟨427228526726676330474839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1139276071271136881266237 427228526726676330474839)
          ·
            refine ⟨640842790090014495712259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427228526726676330474839 640842790090014495712259)
            ·
              refine ⟨961264185135021743568389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 640842790090014495712259 961264185135021743568389)
              ·
                refine ⟨180237034712816576919073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 961264185135021743568389 180237034712816576919073)
                ·
                  refine ⟨135177776034612432689305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180237034712816576919073 135177776034612432689305)
                  ·
                    rfl

theorem cell20_296165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_296165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296165 prefixEnd_296165 := by exact prefixLift 296165
  have htrace : WordTrace (prefixWord ++ tailWord_296165) baseStart_296165 baseEnd_296165 := by
    simpa [prefixWord, tailWord_296165, baseEnd_296165] using wordTrace_append hprefix tailTrace_296165
  have hstable : (prefixWord ++ tailWord_296165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296165).length < 2 ^ (prefixWord ++ tailWord_296165).sum := by decide
  have hdescent : baseEnd_296165 < baseStart_296165 := by decide
  rcases family_descends (prefixWord ++ tailWord_296165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296193 : List Nat := [1, 2, 4, 1, 1, 4, 3, 4]
def baseStart_296193 : Nat := 118140960795 + 296193 * 2 ^ 59
def prefixEnd_296193 : Nat := 4983230072969 + 3 ^ 40 * 296193 * 2
def baseEnd_296193 : Nat := 45063518665856259918619

theorem tailTrace_296193 : CollatzResearch.WordTrace tailWord_296193 prefixEnd_296193 45063518665856259918619 := by
  unfold tailWord_296193
  simp only [CollatzResearch.WordTrace]
  refine ⟨10803046215950821582173233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7202030810633881054782155 10803046215950821582173233)
  ·
    refine ⟨8102284661963116186629925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10803046215950821582173233 8102284661963116186629925)
    ·
      refine ⟨1519178374118084284993111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8102284661963116186629925 1519178374118084284993111)
      ·
        refine ⟨2278767561177126427489667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519178374118084284993111 2278767561177126427489667)
        ·
          refine ⟨3418151341765689641234501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278767561177126427489667 3418151341765689641234501)
          ·
            refine ⟨640903376581066807731469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3418151341765689641234501 640903376581066807731469)
            ·
              refine ⟨240338766217900052899301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 640903376581066807731469 240338766217900052899301)
              ·
                refine ⟨45063518665856259918619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240338766217900052899301 45063518665856259918619)
                ·
                  rfl

theorem cell20_296193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 4].length) (baseStart_296193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296193 prefixEnd_296193 := by exact prefixLift 296193
  have htrace : WordTrace (prefixWord ++ tailWord_296193) baseStart_296193 baseEnd_296193 := by
    simpa [prefixWord, tailWord_296193, baseEnd_296193] using wordTrace_append hprefix tailTrace_296193
  have hstable : (prefixWord ++ tailWord_296193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296193).length < 2 ^ (prefixWord ++ tailWord_296193).sum := by decide
  have hdescent : baseEnd_296193 < baseStart_296193 := by decide
  rcases family_descends (prefixWord ++ tailWord_296193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296210 : List Nat := [3, 2, 4, 2, 1, 1, 7]
def baseStart_296210 : Nat := 118140960795 + 296210 * 2 ^ 59
def prefixEnd_296210 : Nat := 4983230072969 + 3 ^ 40 * 296210 * 2
def baseEnd_296210 : Nat := 15022035028976919576569

theorem tailTrace_296210 : CollatzResearch.WordTrace tailWord_296210 prefixEnd_296210 15022035028976919576569 := by
  unfold tailWord_296210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2700916564222308371385521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7202444171259488990361389 2700916564222308371385521)
  ·
    refine ⟨2025687423166731278539141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2700916564222308371385521 2025687423166731278539141)
    ·
      refine ⟨379816391843762114726089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2025687423166731278539141 379816391843762114726089)
      ·
        refine ⟨284862293882821586044567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 379816391843762114726089 284862293882821586044567)
        ·
          refine ⟨427293440824232379066851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284862293882821586044567 427293440824232379066851)
          ·
            refine ⟨640940161236348568600277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427293440824232379066851 640940161236348568600277)
            ·
              refine ⟨15022035028976919576569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 640940161236348568600277 15022035028976919576569)
              ·
                rfl

theorem cell20_296210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 7].length) (baseStart_296210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296210 prefixEnd_296210 := by exact prefixLift 296210
  have htrace : WordTrace (prefixWord ++ tailWord_296210) baseStart_296210 baseEnd_296210 := by
    simpa [prefixWord, tailWord_296210, baseEnd_296210] using wordTrace_append hprefix tailTrace_296210
  have hstable : (prefixWord ++ tailWord_296210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296210).length < 2 ^ (prefixWord ++ tailWord_296210).sum := by decide
  have hdescent : baseEnd_296210 < baseStart_296210 := by decide
  rcases family_descends (prefixWord ++ tailWord_296210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296224 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 4]
def baseStart_296224 : Nat := 118140960795 + 296224 * 2 ^ 59
def prefixEnd_296224 : Nat := 4983230072969 + 3 ^ 40 * 296224 * 2
def baseEnd_296224 : Nat := 135204705242270449722397

theorem tailTrace_296224 : CollatzResearch.WordTrace tailWord_296224 prefixEnd_296224 135204705242270449722397 := by
  unfold tailWord_296224
  simp only [CollatzResearch.WordTrace]
  refine ⟨5402088439419256938275863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7202784585892342584367817 5402088439419256938275863)
  ·
    refine ⟨8103132659128885407413795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5402088439419256938275863 8103132659128885407413795)
    ·
      refine ⟨12154698988693328111120693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8103132659128885407413795 12154698988693328111120693)
      ·
        refine ⟨1139503030189999510417565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12154698988693328111120693 1139503030189999510417565)
        ·
          refine ⟨427313636321249816406587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1139503030189999510417565 427313636321249816406587)
          ·
            refine ⟨640970454481874724609881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427313636321249816406587 640970454481874724609881)
            ·
              refine ⟨480727840861406043457411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640970454481874724609881 480727840861406043457411)
              ·
                refine ⟨721091761292109065186117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480727840861406043457411 721091761292109065186117)
                ·
                  refine ⟨135204705242270449722397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 721091761292109065186117 135204705242270449722397)
                  ·
                    rfl

theorem cell20_296224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_296224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296224 prefixEnd_296224 := by exact prefixLift 296224
  have htrace : WordTrace (prefixWord ++ tailWord_296224) baseStart_296224 baseEnd_296224 := by
    simpa [prefixWord, tailWord_296224, baseEnd_296224] using wordTrace_append hprefix tailTrace_296224
  have hstable : (prefixWord ++ tailWord_296224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296224).length < 2 ^ (prefixWord ++ tailWord_296224).sum := by decide
  have hdescent : baseEnd_296224 < baseStart_296224 := by decide
  rcases family_descends (prefixWord ++ tailWord_296224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296234 : List Nat := [3, 1, 4, 2, 1, 2, 3, 1, 3]
def baseStart_296234 : Nat := 118140960795 + 296234 * 2 ^ 59
def prefixEnd_296234 : Nat := 4983230072969 + 3 ^ 40 * 296234 * 2
def baseEnd_296234 : Nat := 135209269514754859389023

theorem tailTrace_296234 : CollatzResearch.WordTrace tailWord_296234 prefixEnd_296234 135209269514754859389023 := by
  unfold tailWord_296234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2701135402200571396103939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7203027739201523722943837 2701135402200571396103939)
  ·
    refine ⟨4051703103300857094155909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2701135402200571396103939 4051703103300857094155909)
    ·
      refine ⟨759694331868910705154233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4051703103300857094155909 759694331868910705154233)
      ·
        refine ⟨569770748901683028865675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 759694331868910705154233 569770748901683028865675)
        ·
          refine ⟨854656123352524543298513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569770748901683028865675 854656123352524543298513)
          ·
            refine ⟨640992092514393407473885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 854656123352524543298513 640992092514393407473885)
            ·
              refine ⟨240372034692897527802707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 640992092514393407473885 240372034692897527802707)
              ·
                refine ⟨360558052039346291704061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240372034692897527802707 360558052039346291704061)
                ·
                  refine ⟨135209269514754859389023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360558052039346291704061 135209269514754859389023)
                  ·
                    rfl

theorem cell20_296234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_296234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296234 prefixEnd_296234 := by exact prefixLift 296234
  have htrace : WordTrace (prefixWord ++ tailWord_296234) baseStart_296234 baseEnd_296234 := by
    simpa [prefixWord, tailWord_296234, baseEnd_296234] using wordTrace_append hprefix tailTrace_296234
  have hstable : (prefixWord ++ tailWord_296234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296234).length < 2 ^ (prefixWord ++ tailWord_296234).sum := by decide
  have hdescent : baseEnd_296234 < baseStart_296234 := by decide
  rcases family_descends (prefixWord ++ tailWord_296234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296245 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 4]
def baseStart_296245 : Nat := 118140960795 + 296245 * 2 ^ 59
def prefixEnd_296245 : Nat := 4983230072969 + 3 ^ 40 * 296245 * 2
def baseEnd_296245 : Nat := 135214290214487710022311

theorem tailTrace_296245 : CollatzResearch.WordTrace tailWord_296245 prefixEnd_296245 135214290214487710022311 := by
  unfold tailWord_296245
  simp only [CollatzResearch.WordTrace]
  refine ⟨10804942811762434463066189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7203295207841622975377459 10804942811762434463066189)
  ·
    refine ⟨4051853554410912923649821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10804942811762434463066189 4051853554410912923649821)
    ·
      refine ⟨1519445082904092346368683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4051853554410912923649821 1519445082904092346368683)
      ·
        refine ⟨2279167624356138519553025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519445082904092346368683 2279167624356138519553025)
        ·
          refine ⟨1709375718267103889664769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2279167624356138519553025 1709375718267103889664769)
          ·
            refine ⟨1282031788700327917248577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1709375718267103889664769 1282031788700327917248577)
            ·
              refine ⟨961523841525245937936433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1282031788700327917248577 961523841525245937936433)
              ·
                refine ⟨721142881143934453452325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 961523841525245937936433 721142881143934453452325)
                ·
                  refine ⟨135214290214487710022311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 721142881143934453452325 135214290214487710022311)
                  ·
                    rfl

theorem cell20_296245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_296245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296245 prefixEnd_296245 := by exact prefixLift 296245
  have htrace : WordTrace (prefixWord ++ tailWord_296245) baseStart_296245 baseEnd_296245 := by
    simpa [prefixWord, tailWord_296245, baseEnd_296245] using wordTrace_append hprefix tailTrace_296245
  have hstable : (prefixWord ++ tailWord_296245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296245).length < 2 ^ (prefixWord ++ tailWord_296245).sum := by decide
  have hdescent : baseEnd_296245 < baseStart_296245 := by decide
  rcases family_descends (prefixWord ++ tailWord_296245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296252 : List Nat := [2, 2, 2, 2, 1, 4, 1, 6]
def baseStart_296252 : Nat := 118140960795 + 296252 * 2 ^ 59
def prefixEnd_296252 : Nat := 4983230072969 + 3 ^ 40 * 296252 * 2
def baseEnd_296252 : Nat := 45072495068408932262983

theorem tailTrace_296252 : CollatzResearch.WordTrace tailWord_296252 prefixEnd_296252 45072495068408932262983 := by
  unfold tailWord_296252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5402599061368537329285505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7203465415158049772380673 5402599061368537329285505)
  ·
    refine ⟨4051949296026402996964129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5402599061368537329285505 4051949296026402996964129)
    ·
      refine ⟨3038961972019802247723097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4051949296026402996964129 3038961972019802247723097)
      ·
        refine ⟨2279221479014851685792323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3038961972019802247723097 2279221479014851685792323)
        ·
          refine ⟨3418832218522277528688485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2279221479014851685792323 3418832218522277528688485)
          ·
            refine ⟨641031040972927036629091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3418832218522277528688485 641031040972927036629091)
            ·
              refine ⟨961546561459390554943637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641031040972927036629091 961546561459390554943637)
              ·
                refine ⟨45072495068408932262983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 961546561459390554943637 45072495068408932262983)
                ·
                  rfl

theorem cell20_296252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_296252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296252 prefixEnd_296252 := by exact prefixLift 296252
  have htrace : WordTrace (prefixWord ++ tailWord_296252) baseStart_296252 baseEnd_296252 := by
    simpa [prefixWord, tailWord_296252, baseEnd_296252] using wordTrace_append hprefix tailTrace_296252
  have hstable : (prefixWord ++ tailWord_296252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296252).length < 2 ^ (prefixWord ++ tailWord_296252).sum := by decide
  have hdescent : baseEnd_296252 < baseStart_296252 := by decide
  rcases family_descends (prefixWord ++ tailWord_296252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296266 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_296266 : Nat := 118140960795 + 296266 * 2 ^ 59
def prefixEnd_296266 : Nat := 4983230072969 + 3 ^ 40 * 296266 * 2
def baseEnd_296266 : Nat := 135223875186704970322225

theorem tailTrace_296266 : CollatzResearch.WordTrace tailWord_296266 prefixEnd_296266 135223875186704970322225 := by
  unfold tailWord_296266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2701427186171588762395163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7203805829790903366387101 2701427186171588762395163)
  ·
    refine ⟨4052140779257383143592745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2701427186171588762395163 4052140779257383143592745)
    ·
      refine ⟨3039105584443037357694559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4052140779257383143592745 3039105584443037357694559)
      ·
        refine ⟨4558658376664556036541839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3039105584443037357694559 4558658376664556036541839)
        ·
          refine ⟨6837987564996834054812759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4558658376664556036541839 6837987564996834054812759)
          ·
            refine ⟨10256981347495251082219139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6837987564996834054812759 10256981347495251082219139)
            ·
              refine ⟨15385472021242876623328709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10256981347495251082219139 15385472021242876623328709)
              ·
                refine ⟨2884776003983039366874133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15385472021242876623328709 2884776003983039366874133)
                ·
                  refine ⟨135223875186704970322225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2884776003983039366874133 135223875186704970322225)
                  ·
                    rfl

theorem cell20_296266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_296266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296266 prefixEnd_296266 := by exact prefixLift 296266
  have htrace : WordTrace (prefixWord ++ tailWord_296266) baseStart_296266 baseEnd_296266 := by
    simpa [prefixWord, tailWord_296266, baseEnd_296266] using wordTrace_append hprefix tailTrace_296266
  have hstable : (prefixWord ++ tailWord_296266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296266).length < 2 ^ (prefixWord ++ tailWord_296266).sum := by decide
  have hdescent : baseEnd_296266 < baseStart_296266 := by decide
  rcases family_descends (prefixWord ++ tailWord_296266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296276 : List Nat := [2, 4, 1, 1, 2, 1, 2, 4, 3]
def baseStart_296276 : Nat := 118140960795 + 296276 * 2 ^ 59
def prefixEnd_296276 : Nat := 4983230072969 + 3 ^ 40 * 296276 * 2
def baseEnd_296276 : Nat := 135228439459189379988851

theorem tailTrace_296276 : CollatzResearch.WordTrace tailWord_296276 prefixEnd_296276 135228439459189379988851 := by
  unfold tailWord_296276
  simp only [CollatzResearch.WordTrace]
  refine ⟨5403036737325063378722341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7204048983100084504963121 5403036737325063378722341)
  ·
    refine ⟨1013069388248449383510439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5403036737325063378722341 1013069388248449383510439)
    ·
      refine ⟨1519604082372674075265659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1013069388248449383510439 1519604082372674075265659)
      ·
        refine ⟨2279406123559011112898489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519604082372674075265659 2279406123559011112898489)
        ·
          refine ⟨1709554592669258334673867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2279406123559011112898489 1709554592669258334673867)
          ·
            refine ⟨2564331889003887502010801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709554592669258334673867 2564331889003887502010801)
            ·
              refine ⟨1923248916752915626508101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2564331889003887502010801 1923248916752915626508101)
              ·
                refine ⟨360609171891171679970269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1923248916752915626508101 360609171891171679970269)
                ·
                  refine ⟨135228439459189379988851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360609171891171679970269 135228439459189379988851)
                  ·
                    rfl

theorem cell20_296276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_296276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296276 prefixEnd_296276 := by exact prefixLift 296276
  have htrace : WordTrace (prefixWord ++ tailWord_296276) baseStart_296276 baseEnd_296276 := by
    simpa [prefixWord, tailWord_296276, baseEnd_296276] using wordTrace_append hprefix tailTrace_296276
  have hstable : (prefixWord ++ tailWord_296276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296276).length < 2 ^ (prefixWord ++ tailWord_296276).sum := by decide
  have hdescent : baseEnd_296276 < baseStart_296276 := by decide
  rcases family_descends (prefixWord ++ tailWord_296276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296279 : List Nat := [1, 1, 3, 2, 3, 3, 3, 2, 2]
def baseStart_296279 : Nat := 118140960795 + 296279 * 2 ^ 59
def prefixEnd_296279 : Nat := 4983230072969 + 3 ^ 40 * 296279 * 2
def baseEnd_296279 : Nat := 135229808740934702888839

theorem tailTrace_296279 : CollatzResearch.WordTrace tailWord_296279 prefixEnd_296279 135229808740934702888839 := by
  unfold tailWord_296279
  simp only [CollatzResearch.WordTrace]
  refine ⟨10806182893639258269803891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7204121929092838846535927 10806182893639258269803891)
  ·
    refine ⟨16209274340458887404705837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10806182893639258269803891 16209274340458887404705837)
    ·
      refine ⟨6078477877672082776764689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16209274340458887404705837 6078477877672082776764689)
      ·
        refine ⟨4558858408254062082573517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6078477877672082776764689 4558858408254062082573517)
        ·
          refine ⟨1709571903095273280965069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4558858408254062082573517 1709571903095273280965069)
          ·
            refine ⟨641089463660727480361901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1709571903095273280965069 641089463660727480361901)
            ·
              refine ⟨240408548872772805135713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 641089463660727480361901 240408548872772805135713)
              ·
                refine ⟨180306411654579603851785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240408548872772805135713 180306411654579603851785)
                ·
                  refine ⟨135229808740934702888839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180306411654579603851785 135229808740934702888839)
                  ·
                    rfl

theorem cell20_296279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 2, 2].length) (baseStart_296279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296279 prefixEnd_296279 := by exact prefixLift 296279
  have htrace : WordTrace (prefixWord ++ tailWord_296279) baseStart_296279 baseEnd_296279 := by
    simpa [prefixWord, tailWord_296279, baseEnd_296279] using wordTrace_append hprefix tailTrace_296279
  have hstable : (prefixWord ++ tailWord_296279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296279).length < 2 ^ (prefixWord ++ tailWord_296279).sum := by decide
  have hdescent : baseEnd_296279 < baseStart_296279 := by decide
  rcases family_descends (prefixWord ++ tailWord_296279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296285 : List Nat := [1, 4, 5, 1, 2, 1, 2, 1, 3]
def baseStart_296285 : Nat := 118140960795 + 296285 * 2 ^ 59
def prefixEnd_296285 : Nat := 4983230072969 + 3 ^ 40 * 296285 * 2
def baseEnd_296285 : Nat := 135232547304425348688815

theorem tailTrace_296285 : CollatzResearch.WordTrace tailWord_296285 prefixEnd_296285 135232547304425348688815 := by
  unfold tailWord_296285
  simp only [CollatzResearch.WordTrace]
  refine ⟨10806401731617521294522309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7204267821078347529681539 10806401731617521294522309)
  ·
    refine ⟨2026200324678285242722933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10806401731617521294522309 2026200324678285242722933)
    ·
      refine ⟨189956280438589241505275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2026200324678285242722933 189956280438589241505275)
      ·
        refine ⟨284934420657883862257913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189956280438589241505275 284934420657883862257913)
        ·
          refine ⟨213700815493412896693435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284934420657883862257913 213700815493412896693435)
          ·
            refine ⟨320551223240119345040153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213700815493412896693435 320551223240119345040153)
            ·
              refine ⟨240413417430089508780115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320551223240119345040153 240413417430089508780115)
              ·
                refine ⟨360620126145134263170173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240413417430089508780115 360620126145134263170173)
                ·
                  refine ⟨135232547304425348688815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360620126145134263170173 135232547304425348688815)
                  ·
                    rfl

theorem cell20_296285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_296285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296285 prefixEnd_296285 := by exact prefixLift 296285
  have htrace : WordTrace (prefixWord ++ tailWord_296285) baseStart_296285 baseEnd_296285 := by
    simpa [prefixWord, tailWord_296285, baseEnd_296285] using wordTrace_append hprefix tailTrace_296285
  have hstable : (prefixWord ++ tailWord_296285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296285).length < 2 ^ (prefixWord ++ tailWord_296285).sum := by decide
  have hdescent : baseEnd_296285 < baseStart_296285 := by decide
  rcases family_descends (prefixWord ++ tailWord_296285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296304 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_296304 : Nat := 118140960795 + 296304 * 2 ^ 59
def prefixEnd_296304 : Nat := 4983230072969 + 3 ^ 40 * 296304 * 2
def baseEnd_296304 : Nat := 135241219422145727055403

theorem tailTrace_296304 : CollatzResearch.WordTrace tailWord_296304 prefixEnd_296304 135241219422145727055403 := by
  unfold tailWord_296304
  simp only [CollatzResearch.WordTrace]
  refine ⟨5403547359274343769731983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7204729812365791692975977 5403547359274343769731983)
  ·
    refine ⟨8105321038911515654597975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5403547359274343769731983 8105321038911515654597975)
    ·
      refine ⟨12157981558367273481896963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8105321038911515654597975 12157981558367273481896963)
      ·
        refine ⟨18236972337550910222845445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12157981558367273481896963 18236972337550910222845445)
        ·
          refine ⟨3419432313290795666783521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18236972337550910222845445 3419432313290795666783521)
          ·
            refine ⟨2564574234968096750087641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3419432313290795666783521 2564574234968096750087641)
            ·
              refine ⟨1923430676226072562565731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2564574234968096750087641 1923430676226072562565731)
              ·
                refine ⟨2885146014339108843848597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1923430676226072562565731 2885146014339108843848597)
                ·
                  refine ⟨135241219422145727055403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2885146014339108843848597 135241219422145727055403)
                  ·
                    rfl

theorem cell20_296304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_296304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296304 prefixEnd_296304 := by exact prefixLift 296304
  have htrace : WordTrace (prefixWord ++ tailWord_296304) baseStart_296304 baseEnd_296304 := by
    simpa [prefixWord, tailWord_296304, baseEnd_296304] using wordTrace_append hprefix tailTrace_296304
  have hstable : (prefixWord ++ tailWord_296304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296304).length < 2 ^ (prefixWord ++ tailWord_296304).sum := by decide
  have hdescent : baseEnd_296304 < baseStart_296304 := by decide
  rcases family_descends (prefixWord ++ tailWord_296304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296311 : List Nat := [1, 1, 3, 1, 1, 2, 3, 8]
def baseStart_296311 : Nat := 118140960795 + 296311 * 2 ^ 59
def prefixEnd_296311 : Nat := 4983230072969 + 3 ^ 40 * 296311 * 2
def baseEnd_296311 : Nat := 45081471470961604607347

theorem tailTrace_296311 : CollatzResearch.WordTrace tailWord_296311 prefixEnd_296311 45081471470961604607347 := by
  unfold tailWord_296311
  simp only [CollatzResearch.WordTrace]
  refine ⟨10807350029523327734968787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7204900019682218489979191 10807350029523327734968787)
  ·
    refine ⟨16211025044284991602453181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10807350029523327734968787 16211025044284991602453181)
    ·
      refine ⟨6079134391606871850919943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16211025044284991602453181 6079134391606871850919943)
      ·
        refine ⟨9118701587410307776379915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6079134391606871850919943 9118701587410307776379915)
        ·
          refine ⟨13678052381115461664569873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9118701587410307776379915 13678052381115461664569873)
          ·
            refine ⟨10258539285836596248427405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13678052381115461664569873 10258539285836596248427405)
            ·
              refine ⟨3846952232188723593160277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10258539285836596248427405 3846952232188723593160277)
              ·
                refine ⟨45081471470961604607347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3846952232188723593160277 45081471470961604607347)
                ·
                  rfl

theorem cell20_296311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 8].length) (baseStart_296311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296311 prefixEnd_296311 := by exact prefixLift 296311
  have htrace : WordTrace (prefixWord ++ tailWord_296311) baseStart_296311 baseEnd_296311 := by
    simpa [prefixWord, tailWord_296311, baseEnd_296311] using wordTrace_append hprefix tailTrace_296311
  have hstable : (prefixWord ++ tailWord_296311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296311).length < 2 ^ (prefixWord ++ tailWord_296311).sum := by decide
  have hdescent : baseEnd_296311 < baseStart_296311 := by decide
  rcases family_descends (prefixWord ++ tailWord_296311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296359 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 4]
def baseStart_296359 : Nat := 118140960795 + 296359 * 2 ^ 59
def prefixEnd_296359 : Nat := 4983230072969 + 3 ^ 40 * 296359 * 2
def baseEnd_296359 : Nat := 135266322920809980221845

theorem tailTrace_296359 : CollatzResearch.WordTrace tailWord_296359 prefixEnd_296359 135266322920809980221845 := by
  unfold tailWord_296359
  simp only [CollatzResearch.WordTrace]
  refine ⟨10809100733349431932716131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7206067155566287955144087 10809100733349431932716131)
  ·
    refine ⟨16213651100024147899074197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10809100733349431932716131 16213651100024147899074197)
    ·
      refine ⟨760014895313631932769103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16213651100024147899074197 760014895313631932769103)
      ·
        refine ⟨1140022342970447899153655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760014895313631932769103 1140022342970447899153655)
        ·
          refine ⟨1710033514455671848730483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140022342970447899153655 1710033514455671848730483)
          ·
            refine ⟨2565050271683507773095725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710033514455671848730483 2565050271683507773095725)
            ·
              refine ⟨961893851881315414910897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2565050271683507773095725 961893851881315414910897)
              ·
                refine ⟨721420388910986561183173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 961893851881315414910897 721420388910986561183173)
                ·
                  refine ⟨135266322920809980221845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 721420388910986561183173 135266322920809980221845)
                  ·
                    rfl

theorem cell20_296359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_296359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296359 prefixEnd_296359 := by exact prefixLift 296359
  have htrace : WordTrace (prefixWord ++ tailWord_296359) baseStart_296359 baseEnd_296359 := by
    simpa [prefixWord, tailWord_296359, baseEnd_296359] using wordTrace_append hprefix tailTrace_296359
  have hstable : (prefixWord ++ tailWord_296359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296359).length < 2 ^ (prefixWord ++ tailWord_296359).sum := by decide
  have hdescent : baseEnd_296359 < baseStart_296359 := by decide
  rcases family_descends (prefixWord ++ tailWord_296359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296421 : List Nat := [1, 3, 1, 5, 1, 1, 4, 4]
def baseStart_296421 : Nat := 118140960795 + 296421 * 2 ^ 59
def prefixEnd_296421 : Nat := 4983230072969 + 3 ^ 40 * 296421 * 2
def baseEnd_296421 : Nat := 45098207136737773384975

theorem tailTrace_296421 : CollatzResearch.WordTrace tailWord_296421 prefixEnd_296421 45098207136737773384975 := by
  unfold tailWord_296421
  simp only [CollatzResearch.WordTrace]
  refine ⟨10811362059124816521473117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7207574706083211014315411 10811362059124816521473117)
  ·
    refine ⟨4054260772171806195552419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10811362059124816521473117 4054260772171806195552419)
    ·
      refine ⟨6081391158257709293328629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4054260772171806195552419 6081391158257709293328629)
      ·
        refine ⟨570130421086660246249559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6081391158257709293328629 570130421086660246249559)
        ·
          refine ⟨855195631629990369374339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570130421086660246249559 855195631629990369374339)
          ·
            refine ⟨1282793447444985554061509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855195631629990369374339 1282793447444985554061509)
            ·
              refine ⟨240523771395934791386533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1282793447444985554061509 240523771395934791386533)
              ·
                refine ⟨45098207136737773384975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240523771395934791386533 45098207136737773384975)
                ·
                  rfl

theorem cell20_296421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 4].length) (baseStart_296421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296421 prefixEnd_296421 := by exact prefixLift 296421
  have htrace : WordTrace (prefixWord ++ tailWord_296421) baseStart_296421 baseEnd_296421 := by
    simpa [prefixWord, tailWord_296421, baseEnd_296421] using wordTrace_append hprefix tailTrace_296421
  have hstable : (prefixWord ++ tailWord_296421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296421).length < 2 ^ (prefixWord ++ tailWord_296421).sum := by decide
  have hdescent : baseEnd_296421 < baseStart_296421 := by decide
  rcases family_descends (prefixWord ++ tailWord_296421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296435 : List Nat := [1, 1, 1, 2, 2, 2, 2, 7, 2]
def baseStart_296435 : Nat := 118140960795 + 296435 * 2 ^ 59
def prefixEnd_296435 : Nat := 4983230072969 + 3 ^ 40 * 296435 * 2
def baseEnd_296435 : Nat := 135301011391691493688201

theorem tailTrace_296435 : CollatzResearch.WordTrace tailWord_296435 prefixEnd_296435 135301011391691493688201 := by
  unfold tailWord_296435
  simp only [CollatzResearch.WordTrace]
  refine ⟨10811872681074096912482759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7207915120716064608321839 10811872681074096912482759)
  ·
    refine ⟨16217809021611145368724139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10811872681074096912482759 16217809021611145368724139)
    ·
      refine ⟨24326713532416718053086209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16217809021611145368724139 24326713532416718053086209)
      ·
        refine ⟨18245035149312538539814657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24326713532416718053086209 18245035149312538539814657)
        ·
          refine ⟨13683776361984403904860993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18245035149312538539814657 13683776361984403904860993)
          ·
            refine ⟨10262832271488302928645745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13683776361984403904860993 10262832271488302928645745)
            ·
              refine ⟨7697124203616227196484309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10262832271488302928645745 7697124203616227196484309)
              ·
                refine ⟨180401348522255324917601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7697124203616227196484309 180401348522255324917601)
                ·
                  refine ⟨135301011391691493688201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180401348522255324917601 135301011391691493688201)
                  ·
                    rfl

theorem cell20_296435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 2].length) (baseStart_296435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296435 prefixEnd_296435 := by exact prefixLift 296435
  have htrace : WordTrace (prefixWord ++ tailWord_296435) baseStart_296435 baseEnd_296435 := by
    simpa [prefixWord, tailWord_296435, baseEnd_296435] using wordTrace_append hprefix tailTrace_296435
  have hstable : (prefixWord ++ tailWord_296435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296435).length < 2 ^ (prefixWord ++ tailWord_296435).sum := by decide
  have hdescent : baseEnd_296435 < baseStart_296435 := by decide
  rcases family_descends (prefixWord ++ tailWord_296435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296462 : List Nat := [4, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_296462 : Nat := 118140960795 + 296462 * 2 ^ 59
def prefixEnd_296462 : Nat := 4983230072969 + 3 ^ 40 * 296462 * 2
def baseEnd_296462 : Nat := 135313334927399399788091

theorem tailTrace_296462 : CollatzResearch.WordTrace tailWord_296462 prefixEnd_296462 135313334927399399788091 := by
  unfold tailWord_296462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1351607181497035065464455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7208571634650853682477093 1351607181497035065464455)
  ·
    refine ⟨2027410772245552598196683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1351607181497035065464455 2027410772245552598196683)
    ·
      refine ⟨3041116158368328897295025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2027410772245552598196683 3041116158368328897295025)
      ·
        refine ⟨2280837118776246672971269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3041116158368328897295025 2280837118776246672971269)
        ·
          refine ⟨427656959770546251182113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2280837118776246672971269 427656959770546251182113)
          ·
            refine ⟨320742719827909688386585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 427656959770546251182113 320742719827909688386585)
            ·
              refine ⟨240557039870932266289939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320742719827909688386585 240557039870932266289939)
              ·
                refine ⟨360835559806398399434909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240557039870932266289939 360835559806398399434909)
                ·
                  refine ⟨135313334927399399788091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360835559806398399434909 135313334927399399788091)
                  ·
                    rfl

theorem cell20_296462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_296462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296462 prefixEnd_296462 := by exact prefixLift 296462
  have htrace : WordTrace (prefixWord ++ tailWord_296462) baseStart_296462 baseEnd_296462 := by
    simpa [prefixWord, tailWord_296462, baseEnd_296462] using wordTrace_append hprefix tailTrace_296462
  have hstable : (prefixWord ++ tailWord_296462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296462).length < 2 ^ (prefixWord ++ tailWord_296462).sum := by decide
  have hdescent : baseEnd_296462 < baseStart_296462 := by decide
  rcases family_descends (prefixWord ++ tailWord_296462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296480 : List Nat := [2, 1, 1, 6, 1, 1, 2, 6]
def baseStart_296480 : Nat := 118140960795 + 296480 * 2 ^ 59
def prefixEnd_296480 : Nat := 4983230072969 + 3 ^ 40 * 296480 * 2
def baseEnd_296480 : Nat := 45107183539290445729339

theorem tailTrace_296480 : CollatzResearch.WordTrace tailWord_296480 prefixEnd_296480 45107183539290445729339 := by
  unfold tailWord_296480
  simp only [CollatzResearch.WordTrace]
  refine ⟨5406756982955534798935447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7209009310607379731913929 5406756982955534798935447)
  ·
    refine ⟨8110135474433302198403171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5406756982955534798935447 8110135474433302198403171)
    ·
      refine ⟨12165203211649953297604757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8110135474433302198403171 12165203211649953297604757)
      ·
        refine ⟨570243900546091560825223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12165203211649953297604757 570243900546091560825223)
        ·
          refine ⟨855365850819137341237835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570243900546091560825223 855365850819137341237835)
          ·
            refine ⟨1283048776228706011856753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855365850819137341237835 1283048776228706011856753)
            ·
              refine ⟨962286582171529508892565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1283048776228706011856753 962286582171529508892565)
              ·
                refine ⟨45107183539290445729339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 962286582171529508892565 45107183539290445729339)
                ·
                  rfl

theorem cell20_296480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_296480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296480 prefixEnd_296480 := by exact prefixLift 296480
  have htrace : WordTrace (prefixWord ++ tailWord_296480) baseStart_296480 baseEnd_296480 := by
    simpa [prefixWord, tailWord_296480, baseEnd_296480] using wordTrace_append hprefix tailTrace_296480
  have hstable : (prefixWord ++ tailWord_296480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296480).length < 2 ^ (prefixWord ++ tailWord_296480).sum := by decide
  have hdescent : baseEnd_296480 < baseStart_296480 := by decide
  rcases family_descends (prefixWord ++ tailWord_296480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296490 : List Nat := [3, 1, 4, 1, 1, 1, 2, 5, 2]
def baseStart_296490 : Nat := 118140960795 + 296490 * 2 ^ 59
def prefixEnd_296490 : Nat := 4983230072969 + 3 ^ 40 * 296490 * 2
def baseEnd_296490 : Nat := 135326114890355746854643

theorem tailTrace_296490 : CollatzResearch.WordTrace tailWord_296490 prefixEnd_296490 135326114890355746854643 := by
  unfold tailWord_296490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2703469673968710326433731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7209252463916560870489949 2703469673968710326433731)
  ·
    refine ⟨4055204510953065489650597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2703469673968710326433731 4055204510953065489650597)
    ·
      refine ⟨760350845803699779309487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4055204510953065489650597 760350845803699779309487)
      ·
        refine ⟨1140526268705549668964231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760350845803699779309487 1140526268705549668964231)
        ·
          refine ⟨1710789403058324503446347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140526268705549668964231 1710789403058324503446347)
          ·
            refine ⟨2566184104587486755169521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710789403058324503446347 2566184104587486755169521)
            ·
              refine ⟨1924638078440615066377141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2566184104587486755169521 1924638078440615066377141)
              ·
                refine ⟨180434819853807662472857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1924638078440615066377141 180434819853807662472857)
                ·
                  refine ⟨135326114890355746854643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180434819853807662472857 135326114890355746854643)
                  ·
                    rfl

theorem cell20_296490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_296490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296490 prefixEnd_296490 := by exact prefixLift 296490
  have htrace : WordTrace (prefixWord ++ tailWord_296490) baseStart_296490 baseEnd_296490 := by
    simpa [prefixWord, tailWord_296490, baseEnd_296490] using wordTrace_append hprefix tailTrace_296490
  have hstable : (prefixWord ++ tailWord_296490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296490).length < 2 ^ (prefixWord ++ tailWord_296490).sum := by decide
  have hdescent : baseEnd_296490 < baseStart_296490 := by decide
  rcases family_descends (prefixWord ++ tailWord_296490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296501 : List Nat := [1, 3, 3, 1, 1, 11]
def baseStart_296501 : Nat := 118140960795 + 296501 * 2 ^ 59
def prefixEnd_296501 : Nat := 4983230072969 + 3 ^ 40 * 296501 * 2
def baseEnd_296501 : Nat := 5012264281114392499553

theorem tailTrace_296501 : CollatzResearch.WordTrace tailWord_296501 prefixEnd_296501 5012264281114392499553 := by
  unfold tailWord_296501
  simp only [CollatzResearch.WordTrace]
  refine ⟨10814279898834990184385357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7209519932556660122923571 10814279898834990184385357)
  ·
    refine ⟨4055354962063121319144509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10814279898834990184385357 4055354962063121319144509)
    ·
      refine ⟨1520758110773670494679191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4055354962063121319144509 1520758110773670494679191)
      ·
        refine ⟨2281137166160505742018787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1520758110773670494679191 2281137166160505742018787)
        ·
          refine ⟨3421705749240758613028181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2281137166160505742018787 3421705749240758613028181)
          ·
            refine ⟨5012264281114392499553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3421705749240758613028181 5012264281114392499553)
            ·
              rfl

theorem cell20_296501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 11].length) (baseStart_296501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296501 prefixEnd_296501 := by exact prefixLift 296501
  have htrace : WordTrace (prefixWord ++ tailWord_296501) baseStart_296501 baseEnd_296501 := by
    simpa [prefixWord, tailWord_296501, baseEnd_296501] using wordTrace_append hprefix tailTrace_296501
  have hstable : (prefixWord ++ tailWord_296501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296501).length < 2 ^ (prefixWord ++ tailWord_296501).sum := by decide
  have hdescent : baseEnd_296501 < baseStart_296501 := by decide
  rcases family_descends (prefixWord ++ tailWord_296501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296504 : List Nat := [2, 1, 2, 1, 4, 3, 2, 2, 3]
def baseStart_296504 : Nat := 118140960795 + 296504 * 2 ^ 59
def prefixEnd_296504 : Nat := 4983230072969 + 3 ^ 40 * 296504 * 2
def baseEnd_296504 : Nat := 135332504871833920387919

theorem tailTrace_296504 : CollatzResearch.WordTrace tailWord_296504 prefixEnd_296504 135332504871833920387919 := by
  unfold tailWord_296504
  simp only [CollatzResearch.WordTrace]
  refine ⟨5407194658912060848372283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7209592878549414464496377 5407194658912060848372283)
  ·
    refine ⟨8110791988368091272558425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5407194658912060848372283 8110791988368091272558425)
    ·
      refine ⟨6083093991276068454418819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8110791988368091272558425 6083093991276068454418819)
      ·
        refine ⟨9124640986914102681628229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6083093991276068454418819 9124640986914102681628229)
        ·
          refine ⟨1710870185046394252805293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9124640986914102681628229 1710870185046394252805293)
          ·
            refine ⟨641576319392397844801985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1710870185046394252805293 641576319392397844801985)
            ·
              refine ⟨481182239544298383601489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641576319392397844801985 481182239544298383601489)
              ·
                refine ⟨360886679658223787701117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481182239544298383601489 360886679658223787701117)
                ·
                  refine ⟨135332504871833920387919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 360886679658223787701117 135332504871833920387919)
                  ·
                    rfl

theorem cell20_296504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_296504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296504 prefixEnd_296504 := by exact prefixLift 296504
  have htrace : WordTrace (prefixWord ++ tailWord_296504) baseStart_296504 baseEnd_296504 := by
    simpa [prefixWord, tailWord_296504, baseEnd_296504] using wordTrace_append hprefix tailTrace_296504
  have hstable : (prefixWord ++ tailWord_296504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296504).length < 2 ^ (prefixWord ++ tailWord_296504).sum := by decide
  have hdescent : baseEnd_296504 < baseStart_296504 := by decide
  rcases family_descends (prefixWord ++ tailWord_296504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296566 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_296566 : Nat := 118140960795 + 296566 * 2 ^ 59
def prefixEnd_296566 : Nat := 4983230072969 + 3 ^ 40 * 296566 * 2
def baseEnd_296566 : Nat := 135360803361237260320999

theorem tailTrace_296566 : CollatzResearch.WordTrace tailWord_296566 prefixEnd_296566 135360803361237260320999 := by
  unfold tailWord_296566
  simp only [CollatzResearch.WordTrace]
  refine ⟨676040665224969142843847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7211100429066337523667701 676040665224969142843847)
  ·
    refine ⟨1014060997837453714265771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 676040665224969142843847 1014060997837453714265771)
    ·
      refine ⟨1521091496756180571398657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1014060997837453714265771 1521091496756180571398657)
      ·
        refine ⟨1140818622567135428548993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1521091496756180571398657 1140818622567135428548993)
        ·
          refine ⟨855613966925351571411745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1140818622567135428548993 855613966925351571411745)
          ·
            refine ⟨641710475194013678558809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 855613966925351571411745 641710475194013678558809)
            ·
              refine ⟨481282856395510258919107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 641710475194013678558809 481282856395510258919107)
              ·
                refine ⟨721924284593265388378661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481282856395510258919107 721924284593265388378661)
                ·
                  refine ⟨135360803361237260320999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 721924284593265388378661 135360803361237260320999)
                  ·
                    rfl

theorem cell20_296566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_296566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296566 prefixEnd_296566 := by exact prefixLift 296566
  have htrace : WordTrace (prefixWord ++ tailWord_296566) baseStart_296566 baseEnd_296566 := by
    simpa [prefixWord, tailWord_296566, baseEnd_296566] using wordTrace_append hprefix tailTrace_296566
  have hstable : (prefixWord ++ tailWord_296566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296566).length < 2 ^ (prefixWord ++ tailWord_296566).sum := by decide
  have hdescent : baseEnd_296566 < baseStart_296566 := by decide
  rcases family_descends (prefixWord ++ tailWord_296566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296621 : List Nat := [1, 5, 2, 1, 1, 1, 5, 2, 2]
def baseStart_296621 : Nat := 118140960795 + 296621 * 2 ^ 59
def prefixEnd_296621 : Nat := 4983230072969 + 3 ^ 40 * 296621 * 2
def baseEnd_296621 : Nat := 135385906859901513487441

theorem tailTrace_296621 : CollatzResearch.WordTrace tailWord_296621 prefixEnd_296621 135385906859901513487441 := by
  unfold tailWord_296621
  simp only [CollatzResearch.WordTrace]
  refine ⟨10818656658400250678753717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7212437772266833785835811 10818656658400250678753717)
  ·
    refine ⟨1014249061725023501133161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10818656658400250678753717 1014249061725023501133161)
    ·
      refine ⟨760686796293767625849871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1014249061725023501133161 760686796293767625849871)
      ·
        refine ⟨1141030194440651438774807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760686796293767625849871 1141030194440651438774807)
        ·
          refine ⟨1711545291660977158162211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1141030194440651438774807 1711545291660977158162211)
          ·
            refine ⟨2567317937491465737243317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1711545291660977158162211 2567317937491465737243317)
            ·
              refine ⟨240686056639824912866561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2567317937491465737243317 240686056639824912866561)
              ·
                refine ⟨180514542479868684649921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240686056639824912866561 180514542479868684649921)
                ·
                  refine ⟨135385906859901513487441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180514542479868684649921 135385906859901513487441)
                  ·
                    rfl

theorem cell20_296621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_296621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296621 prefixEnd_296621 := by exact prefixLift 296621
  have htrace : WordTrace (prefixWord ++ tailWord_296621) baseStart_296621 baseEnd_296621 := by
    simpa [prefixWord, tailWord_296621, baseEnd_296621] using wordTrace_append hprefix tailTrace_296621
  have hstable : (prefixWord ++ tailWord_296621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296621).length < 2 ^ (prefixWord ++ tailWord_296621).sum := by decide
  have hdescent : baseEnd_296621 < baseStart_296621 := by decide
  rcases family_descends (prefixWord ++ tailWord_296621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296639 : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 3]
def baseStart_296639 : Nat := 118140960795 + 296639 * 2 ^ 59
def prefixEnd_296639 : Nat := 4983230072969 + 3 ^ 40 * 296639 * 2
def baseEnd_296639 : Nat := 135394122550373450887367

theorem tailTrace_296639 : CollatzResearch.WordTrace tailWord_296639 prefixEnd_296639 135394122550373450887367 := by
  unfold tailWord_296639
  simp only [CollatzResearch.WordTrace]
  refine ⟨10819313172335039752908971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7212875448223359835272647 10819313172335039752908971)
  ·
    refine ⟨16228969758502559629363457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10819313172335039752908971 16228969758502559629363457)
    ·
      refine ⟨12171727318876919722022593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16228969758502559629363457 12171727318876919722022593)
      ·
        refine ⟨9128795489157689791516945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12171727318876919722022593 9128795489157689791516945)
        ·
          refine ⟨6846596616868267343637709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9128795489157689791516945 6846596616868267343637709)
          ·
            refine ⟨2567473731325600253864141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6846596616868267343637709 2567473731325600253864141)
            ·
              refine ⟨962802649247100095199053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2567473731325600253864141 962802649247100095199053)
              ·
                refine ⟨361050993467662535699645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 962802649247100095199053 361050993467662535699645)
                ·
                  refine ⟨135394122550373450887367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361050993467662535699645 135394122550373450887367)
                  ·
                    rfl

theorem cell20_296639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3].length) (baseStart_296639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296639 prefixEnd_296639 := by exact prefixLift 296639
  have htrace : WordTrace (prefixWord ++ tailWord_296639) baseStart_296639 baseEnd_296639 := by
    simpa [prefixWord, tailWord_296639, baseEnd_296639] using wordTrace_append hprefix tailTrace_296639
  have hstable : (prefixWord ++ tailWord_296639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296639).length < 2 ^ (prefixWord ++ tailWord_296639).sum := by decide
  have hdescent : baseEnd_296639 < baseStart_296639 := by decide
  rcases family_descends (prefixWord ++ tailWord_296639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296663 : List Nat := [1, 1, 3, 2, 1, 3, 2, 5, 2]
def baseStart_296663 : Nat := 118140960795 + 296663 * 2 ^ 59
def prefixEnd_296663 : Nat := 4983230072969 + 3 ^ 40 * 296663 * 2
def baseEnd_296663 : Nat := 135405076804336034087269

theorem tailTrace_296663 : CollatzResearch.WordTrace tailWord_296663 prefixEnd_296663 135405076804336034087269 := by
  unfold tailWord_296663
  simp only [CollatzResearch.WordTrace]
  refine ⟨10820188524248091851782643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7213459016165394567855095 10820188524248091851782643)
  ·
    refine ⟨16230282786372137777673965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10820188524248091851782643 16230282786372137777673965)
    ·
      refine ⟨6086356044889551666627737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16230282786372137777673965 6086356044889551666627737)
      ·
        refine ⟨4564767033667163749970803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6086356044889551666627737 4564767033667163749970803)
        ·
          refine ⟨6847150550500745624956205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4564767033667163749970803 6847150550500745624956205)
          ·
            refine ⟨2567681456437779609358577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6847150550500745624956205 2567681456437779609358577)
            ·
              refine ⟨1925761092328334707018933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2567681456437779609358577 1925761092328334707018933)
              ·
                refine ⟨180540102405781378783025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1925761092328334707018933 180540102405781378783025)
                ·
                  refine ⟨135405076804336034087269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180540102405781378783025 135405076804336034087269)
                  ·
                    rfl

theorem cell20_296663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 2].length) (baseStart_296663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296663 prefixEnd_296663 := by exact prefixLift 296663
  have htrace : WordTrace (prefixWord ++ tailWord_296663) baseStart_296663 baseEnd_296663 := by
    simpa [prefixWord, tailWord_296663, baseEnd_296663] using wordTrace_append hprefix tailTrace_296663
  have hstable : (prefixWord ++ tailWord_296663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296663).length < 2 ^ (prefixWord ++ tailWord_296663).sum := by decide
  have hdescent : baseEnd_296663 < baseStart_296663 := by decide
  rcases family_descends (prefixWord ++ tailWord_296663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296680 : List Nat := [2, 1, 4, 1, 3, 2, 1, 4, 2]
def baseStart_296680 : Nat := 118140960795 + 296680 * 2 ^ 59
def prefixEnd_296680 : Nat := 4983230072969 + 3 ^ 40 * 296680 * 2
def baseEnd_296680 : Nat := 135412836067559530520533

theorem tailTrace_296680 : CollatzResearch.WordTrace tailWord_296680 prefixEnd_296680 135412836067559530520533 := by
  unfold tailWord_296680
  simp only [CollatzResearch.WordTrace]
  refine ⟨5410404282593251877575747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7213872376791002503434329 5410404282593251877575747)
  ·
    refine ⟨8115606423889877816363621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5410404282593251877575747 8115606423889877816363621)
    ·
      refine ⟨1521676204479352090568179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8115606423889877816363621 1521676204479352090568179)
      ·
        refine ⟨2282514306719028135852269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1521676204479352090568179 2282514306719028135852269)
        ·
          refine ⟨855942865019635550944601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2282514306719028135852269 855942865019635550944601)
          ·
            refine ⟨641957148764726663208451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 855942865019635550944601 641957148764726663208451)
            ·
              refine ⟨962935723147089994812677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641957148764726663208451 962935723147089994812677)
              ·
                refine ⟨180550448090079374027377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 962935723147089994812677 180550448090079374027377)
                ·
                  refine ⟨135412836067559530520533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180550448090079374027377 135412836067559530520533)
                  ·
                    rfl

theorem cell20_296680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 2].length) (baseStart_296680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296680 prefixEnd_296680 := by exact prefixLift 296680
  have htrace : WordTrace (prefixWord ++ tailWord_296680) baseStart_296680 baseEnd_296680 := by
    simpa [prefixWord, tailWord_296680, baseEnd_296680] using wordTrace_append hprefix tailTrace_296680
  have hstable : (prefixWord ++ tailWord_296680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296680).length < 2 ^ (prefixWord ++ tailWord_296680).sum := by decide
  have hdescent : baseEnd_296680 < baseStart_296680 := by decide
  rcases family_descends (prefixWord ++ tailWord_296680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296691 : List Nat := [1, 1, 1, 2, 2, 3, 5, 5]
def baseStart_296691 : Nat := 118140960795 + 296691 * 2 ^ 59
def prefixEnd_296691 : Nat := 4983230072969 + 3 ^ 40 * 296691 * 2
def baseEnd_296691 : Nat := 45139285589097460384607

theorem tailTrace_296691 : CollatzResearch.WordTrace tailWord_296691 prefixEnd_296691 45139285589097460384607 := by
  unfold tailWord_296691
  simp only [CollatzResearch.WordTrace]
  refine ⟨10821209768146652633801927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7214139845431101755867951 10821209768146652633801927)
  ·
    refine ⟨16231814652219978950702891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10821209768146652633801927 16231814652219978950702891)
    ·
      refine ⟨24347721978329968426054337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16231814652219978950702891 24347721978329968426054337)
      ·
        refine ⟨18260791483747476319540753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24347721978329968426054337 18260791483747476319540753)
        ·
          refine ⟨13695593612810607239655565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18260791483747476319540753 13695593612810607239655565)
          ·
            refine ⟨5135847604803977714870837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13695593612810607239655565 5135847604803977714870837)
            ·
              refine ⟨481485712950372910769141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5135847604803977714870837 481485712950372910769141)
              ·
                refine ⟨45139285589097460384607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 481485712950372910769141 45139285589097460384607)
                ·
                  rfl

theorem cell20_296691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 5].length) (baseStart_296691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296691 prefixEnd_296691 := by exact prefixLift 296691
  have htrace : WordTrace (prefixWord ++ tailWord_296691) baseStart_296691 baseEnd_296691 := by
    simpa [prefixWord, tailWord_296691, baseEnd_296691] using wordTrace_append hprefix tailTrace_296691
  have hstable : (prefixWord ++ tailWord_296691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296691).length < 2 ^ (prefixWord ++ tailWord_296691).sum := by decide
  have hdescent : baseEnd_296691 < baseStart_296691 := by decide
  rcases family_descends (prefixWord ++ tailWord_296691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296694 : List Nat := [5, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_296694 : Nat := 118140960795 + 296694 * 2 ^ 59
def prefixEnd_296694 : Nat := 4983230072969 + 3 ^ 40 * 296694 * 2
def baseEnd_296694 : Nat := 135419226049037704053809

theorem tailTrace_296694 : CollatzResearch.WordTrace tailWord_296694 prefixEnd_296694 135419226049037704053809 := by
  unfold tailWord_296694
  simp only [CollatzResearch.WordTrace]
  refine ⟨676332449195986509135071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7214212791423856097440757 676332449195986509135071)
  ·
    refine ⟨1014498673793979763702607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 676332449195986509135071 1014498673793979763702607)
    ·
      refine ⟨1521748010690969645553911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1014498673793979763702607 1521748010690969645553911)
      ·
        refine ⟨2282622016036454468330867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1521748010690969645553911 2282622016036454468330867)
        ·
          refine ⟨3423933024054681702496301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2282622016036454468330867 3423933024054681702496301)
          ·
            refine ⟨1283974884020505638436113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3423933024054681702496301 1283974884020505638436113)
            ·
              refine ⟨962981163015379228827085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1283974884020505638436113 962981163015379228827085)
              ·
                refine ⟨361117936130767210810157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 962981163015379228827085 361117936130767210810157)
                ·
                  refine ⟨135419226049037704053809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361117936130767210810157 135419226049037704053809)
                  ·
                    rfl

theorem cell20_296694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_296694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296694 prefixEnd_296694 := by exact prefixLift 296694
  have htrace : WordTrace (prefixWord ++ tailWord_296694) baseStart_296694 baseEnd_296694 := by
    simpa [prefixWord, tailWord_296694, baseEnd_296694] using wordTrace_append hprefix tailTrace_296694
  have hstable : (prefixWord ++ tailWord_296694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296694).length < 2 ^ (prefixWord ++ tailWord_296694).sum := by decide
  have hdescent : baseEnd_296694 < baseStart_296694 := by decide
  rcases family_descends (prefixWord ++ tailWord_296694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296698 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_296698 : Nat := 118140960795 + 296698 * 2 ^ 59
def prefixEnd_296698 : Nat := 4983230072969 + 3 ^ 40 * 296698 * 2
def baseEnd_296698 : Nat := 135421051758031467920459

theorem tailTrace_296698 : CollatzResearch.WordTrace tailWord_296698 prefixEnd_296698 135421051758031467920459 := by
  unfold tailWord_296698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2705366269780323207326687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7214310052747528552871165 2705366269780323207326687)
  ·
    refine ⟨4058049404670484810990031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2705366269780323207326687 4058049404670484810990031)
    ·
      refine ⟨6087074107005727216485047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4058049404670484810990031 6087074107005727216485047)
      ·
        refine ⟨9130611160508590824727571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6087074107005727216485047 9130611160508590824727571)
        ·
          refine ⟨13695916740762886237091357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9130611160508590824727571 13695916740762886237091357)
          ·
            refine ⟨5135968777786082338909259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13695916740762886237091357 5135968777786082338909259)
            ·
              refine ⟨7703953166679123508363889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5135968777786082338909259 7703953166679123508363889)
              ·
                refine ⟨5777964875009342631272917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7703953166679123508363889 5777964875009342631272917)
                ·
                  refine ⟨135421051758031467920459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5777964875009342631272917 135421051758031467920459)
                  ·
                    rfl

theorem cell20_296698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_296698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296698 prefixEnd_296698 := by exact prefixLift 296698
  have htrace : WordTrace (prefixWord ++ tailWord_296698) baseStart_296698 baseEnd_296698 := by
    simpa [prefixWord, tailWord_296698, baseEnd_296698] using wordTrace_append hprefix tailTrace_296698
  have hstable : (prefixWord ++ tailWord_296698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296698).length < 2 ^ (prefixWord ++ tailWord_296698).sum := by decide
  have hdescent : baseEnd_296698 < baseStart_296698 := by decide
  rcases family_descends (prefixWord ++ tailWord_296698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296724 : List Nat := [2, 4, 4, 1, 2, 1, 1, 2, 3]
def baseStart_296724 : Nat := 118140960795 + 296724 * 2 ^ 59
def prefixEnd_296724 : Nat := 4983230072969 + 3 ^ 40 * 296724 * 2
def baseEnd_296724 : Nat := 135432918866490933053687

theorem tailTrace_296724 : CollatzResearch.WordTrace tailWord_296724 prefixEnd_296724 135432918866490933053687 := by
  unfold tailWord_296724
  simp only [CollatzResearch.WordTrace]
  refine ⟨5411206688513549634876613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7214942251351399513168817 5411206688513549634876613)
  ·
    refine ⟨1014601254096290556539365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5411206688513549634876613 1014601254096290556539365)
    ·
      refine ⟨190237735143054479351131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1014601254096290556539365 190237735143054479351131)
      ·
        refine ⟨285356602714581719026697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190237735143054479351131 285356602714581719026697)
        ·
          refine ⟨214017452035936289270023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285356602714581719026697 214017452035936289270023)
          ·
            refine ⟨321026178053904433905035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214017452035936289270023 321026178053904433905035)
            ·
              refine ⟨481539267080856650857553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321026178053904433905035 481539267080856650857553)
              ·
                refine ⟨361154450310642488143165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481539267080856650857553 361154450310642488143165)
                ·
                  refine ⟨135432918866490933053687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361154450310642488143165 135432918866490933053687)
                  ·
                    rfl

theorem cell20_296724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_296724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296724 prefixEnd_296724 := by exact prefixLift 296724
  have htrace : WordTrace (prefixWord ++ tailWord_296724) baseStart_296724 baseEnd_296724 := by
    simpa [prefixWord, tailWord_296724, baseEnd_296724] using wordTrace_append hprefix tailTrace_296724
  have hstable : (prefixWord ++ tailWord_296724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296724).length < 2 ^ (prefixWord ++ tailWord_296724).sum := by decide
  have hdescent : baseEnd_296724 < baseStart_296724 := by decide
  rcases family_descends (prefixWord ++ tailWord_296724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296739 : List Nat := [1, 1, 1, 4, 2, 1, 4, 4, 2]
def baseStart_296739 : Nat := 118140960795 + 296739 * 2 ^ 59
def prefixEnd_296739 : Nat := 4983230072969 + 3 ^ 40 * 296739 * 2
def baseEnd_296739 : Nat := 135439765275217547553625

theorem tailTrace_296739 : CollatzResearch.WordTrace tailWord_296739 prefixEnd_296739 135439765275217547553625 := by
  unfold tailWord_296739
  simp only [CollatzResearch.WordTrace]
  refine ⟨10822960471972756831549271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7215306981315171221032847 10822960471972756831549271)
  ·
    refine ⟨16234440707959135247323907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10822960471972756831549271 16234440707959135247323907)
    ·
      refine ⟨24351661061938702870985861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16234440707959135247323907 24351661061938702870985861)
      ·
        refine ⟨4565936449113506788309849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24351661061938702870985861 4565936449113506788309849)
        ·
          refine ⟨3424452336835130091232387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4565936449113506788309849 3424452336835130091232387)
          ·
            refine ⟨5136678505252695136848581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3424452336835130091232387 5136678505252695136848581)
            ·
              refine ⟨963127219734880338159109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5136678505252695136848581 963127219734880338159109)
              ·
                refine ⟨180586353700290063404833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 963127219734880338159109 180586353700290063404833)
                ·
                  refine ⟨135439765275217547553625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180586353700290063404833 135439765275217547553625)
                  ·
                    rfl

theorem cell20_296739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 2].length) (baseStart_296739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296739 prefixEnd_296739 := by exact prefixLift 296739
  have htrace : WordTrace (prefixWord ++ tailWord_296739) baseStart_296739 baseEnd_296739 := by
    simpa [prefixWord, tailWord_296739, baseEnd_296739] using wordTrace_append hprefix tailTrace_296739
  have hstable : (prefixWord ++ tailWord_296739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296739).length < 2 ^ (prefixWord ++ tailWord_296739).sum := by decide
  have hdescent : baseEnd_296739 < baseStart_296739 := by decide
  rcases family_descends (prefixWord ++ tailWord_296739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296760 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 4]
def baseStart_296760 : Nat := 118140960795 + 296760 * 2 ^ 59
def prefixEnd_296760 : Nat := 4983230072969 + 3 ^ 40 * 296760 * 2
def baseEnd_296760 : Nat := 135449350247434807853539

theorem tailTrace_296760 : CollatzResearch.WordTrace tailWord_296760 prefixEnd_296760 135449350247434807853539 := by
  unfold tailWord_296760
  simp only [CollatzResearch.WordTrace]
  refine ⟨5411863202448338709031867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7215817603264451612042489 5411863202448338709031867)
  ·
    refine ⟨8117794803672508063547801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5411863202448338709031867 8117794803672508063547801)
    ·
      refine ⟨6088346102754381047660851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8117794803672508063547801 6088346102754381047660851)
      ·
        refine ⟨9132519154131571571491277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6088346102754381047660851 9132519154131571571491277)
        ·
          refine ⟨3424694682799339339309229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9132519154131571571491277 3424694682799339339309229)
          ·
            refine ⟨1284260506049752252240961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3424694682799339339309229 1284260506049752252240961)
            ·
              refine ⟨963195379537314189180721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1284260506049752252240961 963195379537314189180721)
              ·
                refine ⟨722396534652985641885541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 963195379537314189180721 722396534652985641885541)
                ·
                  refine ⟨135449350247434807853539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 722396534652985641885541 135449350247434807853539)
                  ·
                    rfl

theorem cell20_296760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_296760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296760 prefixEnd_296760 := by exact prefixLift 296760
  have htrace : WordTrace (prefixWord ++ tailWord_296760) baseStart_296760 baseEnd_296760 := by
    simpa [prefixWord, tailWord_296760, baseEnd_296760] using wordTrace_append hprefix tailTrace_296760
  have hstable : (prefixWord ++ tailWord_296760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296760).length < 2 ^ (prefixWord ++ tailWord_296760).sum := by decide
  have hdescent : baseEnd_296760 < baseStart_296760 := by decide
  rcases family_descends (prefixWord ++ tailWord_296760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296794 : List Nat := [3, 1, 1, 2, 1, 3, 5, 2, 2]
def baseStart_296794 : Nat := 118140960795 + 296794 * 2 ^ 59
def prefixEnd_296794 : Nat := 4983230072969 + 3 ^ 40 * 296794 * 2
def baseEnd_296794 : Nat := 135464868773881800720067

theorem tailTrace_296794 : CollatzResearch.WordTrace tailWord_296794 prefixEnd_296794 135464868773881800720067 := by
  unfold tailWord_296794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2706241621693375306200359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7216644324515667483200957 2706241621693375306200359)
  ·
    refine ⟨4059362432540062959300539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2706241621693375306200359 4059362432540062959300539)
    ·
      refine ⟨6089043648810094438950809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4059362432540062959300539 6089043648810094438950809)
      ·
        refine ⟨4566782736607570829213107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6089043648810094438950809 4566782736607570829213107)
        ·
          refine ⟨6850174104911356243819661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4566782736607570829213107 6850174104911356243819661)
          ·
            refine ⟨2568815289341758591432373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6850174104911356243819661 2568815289341758591432373)
            ·
              refine ⟨240826433375789867946785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2568815289341758591432373 240826433375789867946785)
              ·
                refine ⟨180619825031842400960089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240826433375789867946785 180619825031842400960089)
                ·
                  refine ⟨135464868773881800720067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180619825031842400960089 135464868773881800720067)
                  ·
                    rfl

theorem cell20_296794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_296794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296794 prefixEnd_296794 := by exact prefixLift 296794
  have htrace : WordTrace (prefixWord ++ tailWord_296794) baseStart_296794 baseEnd_296794 := by
    simpa [prefixWord, tailWord_296794, baseEnd_296794] using wordTrace_append hprefix tailTrace_296794
  have hstable : (prefixWord ++ tailWord_296794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296794).length < 2 ^ (prefixWord ++ tailWord_296794).sum := by decide
  have hdescent : baseEnd_296794 < baseStart_296794 := by decide
  rcases family_descends (prefixWord ++ tailWord_296794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296804 : List Nat := [2, 3, 1, 1, 6, 1, 2, 1, 3]
def baseStart_296804 : Nat := 118140960795 + 296804 * 2 ^ 59
def prefixEnd_296804 : Nat := 4983230072969 + 3 ^ 40 * 296804 * 2
def baseEnd_296804 : Nat := 135469433046366210386693

theorem tailTrace_296804 : CollatzResearch.WordTrace tailWord_296804 prefixEnd_296804 135469433046366210386693 := by
  unfold tailWord_296804
  simp only [CollatzResearch.WordTrace]
  refine ⟨5412665608368636466332733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7216887477824848621776977 5412665608368636466332733)
  ·
    refine ⟨2029749603138238674874775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5412665608368636466332733 2029749603138238674874775)
    ·
      refine ⟨3044624404707358012312163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2029749603138238674874775 3044624404707358012312163)
      ·
        refine ⟨4566936607061037018468245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3044624404707358012312163 4566936607061037018468245)
        ·
          refine ⟨214075153455986110240699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4566936607061037018468245 214075153455986110240699)
          ·
            refine ⟨321112730183979165361049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214075153455986110240699 321112730183979165361049)
            ·
              refine ⟨240834547637984374020787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321112730183979165361049 240834547637984374020787)
              ·
                refine ⟨361251821456976561031181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240834547637984374020787 361251821456976561031181)
                ·
                  refine ⟨135469433046366210386693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361251821456976561031181 135469433046366210386693)
                  ·
                    rfl

theorem cell20_296804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_296804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296804 prefixEnd_296804 := by exact prefixLift 296804
  have htrace : WordTrace (prefixWord ++ tailWord_296804) baseStart_296804 baseEnd_296804 := by
    simpa [prefixWord, tailWord_296804, baseEnd_296804] using wordTrace_append hprefix tailTrace_296804
  have hstable : (prefixWord ++ tailWord_296804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296804).length < 2 ^ (prefixWord ++ tailWord_296804).sum := by decide
  have hdescent : baseEnd_296804 < baseStart_296804 := by decide
  rcases family_descends (prefixWord ++ tailWord_296804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296819 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 6]
def baseStart_296819 : Nat := 118140960795 + 296819 * 2 ^ 59
def prefixEnd_296819 : Nat := 4983230072969 + 3 ^ 40 * 296819 * 2
def baseEnd_296819 : Nat := 135476279455092824886631

theorem tailTrace_296819 : CollatzResearch.WordTrace tailWord_296819 prefixEnd_296819 135476279455092824886631 := by
  unfold tailWord_296819
  simp only [CollatzResearch.WordTrace]
  refine ⟨10825878311682930494461511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7217252207788620329641007 10825878311682930494461511)
  ·
    refine ⟨16238817467524395741692267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10825878311682930494461511 16238817467524395741692267)
    ·
      refine ⟨24358226201286593612538401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16238817467524395741692267 24358226201286593612538401)
      ·
        refine ⟨18268669650964945209403801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24358226201286593612538401 18268669650964945209403801)
        ·
          refine ⟨13701502238223708907052851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18268669650964945209403801 13701502238223708907052851)
          ·
            refine ⟨20552253357335563360579277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13701502238223708907052851 20552253357335563360579277)
            ·
              refine ⟨7707095009000836260217229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20552253357335563360579277 7707095009000836260217229)
              ·
                refine ⟨2890160628375313597581461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7707095009000836260217229 2890160628375313597581461)
                ·
                  refine ⟨135476279455092824886631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2890160628375313597581461 135476279455092824886631)
                  ·
                    rfl

theorem cell20_296819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_296819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296819 prefixEnd_296819 := by exact prefixLift 296819
  have htrace : WordTrace (prefixWord ++ tailWord_296819) baseStart_296819 baseEnd_296819 := by
    simpa [prefixWord, tailWord_296819, baseEnd_296819] using wordTrace_append hprefix tailTrace_296819
  have hstable : (prefixWord ++ tailWord_296819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296819).length < 2 ^ (prefixWord ++ tailWord_296819).sum := by decide
  have hdescent : baseEnd_296819 < baseStart_296819 := by decide
  rcases family_descends (prefixWord ++ tailWord_296819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296853 : List Nat := [1, 3, 2, 1, 1, 3, 3, 4, 2]
def baseStart_296853 : Nat := 118140960795 + 296853 * 2 ^ 59
def prefixEnd_296853 : Nat := 4983230072969 + 3 ^ 40 * 296853 * 2
def baseEnd_296853 : Nat := 135491797981539817753159

theorem tailTrace_296853 : CollatzResearch.WordTrace tailWord_296853 prefixEnd_296853 135491797981539817753159 := by
  unfold tailWord_296853
  simp only [CollatzResearch.WordTrace]
  refine ⟨10827118393559754301199213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7218078929039836200799475 10827118393559754301199213)
  ·
    refine ⟨4060169397584907862949705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10827118393559754301199213 4060169397584907862949705)
    ·
      refine ⟨3045127048188680897212279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4060169397584907862949705 3045127048188680897212279)
      ·
        refine ⟨4567690572283021345818419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045127048188680897212279 4567690572283021345818419)
        ·
          refine ⟨6851535858424532018727629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4567690572283021345818419 6851535858424532018727629)
          ·
            refine ⟨2569325946909199507022861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6851535858424532018727629 2569325946909199507022861)
            ·
              refine ⟨963497230090949815133573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2569325946909199507022861 963497230090949815133573)
              ·
                refine ⟨180655730642053090337545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 963497230090949815133573 180655730642053090337545)
                ·
                  refine ⟨135491797981539817753159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180655730642053090337545 135491797981539817753159)
                  ·
                    rfl

theorem cell20_296853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_296853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296853 prefixEnd_296853 := by exact prefixLift 296853
  have htrace : WordTrace (prefixWord ++ tailWord_296853) baseStart_296853 baseEnd_296853 := by
    simpa [prefixWord, tailWord_296853, baseEnd_296853] using wordTrace_append hprefix tailTrace_296853
  have hstable : (prefixWord ++ tailWord_296853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296853).length < 2 ^ (prefixWord ++ tailWord_296853).sum := by decide
  have hdescent : baseEnd_296853 < baseStart_296853 := by decide
  rcases family_descends (prefixWord ++ tailWord_296853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296856 : List Nat := [2, 1, 2, 6, 2, 1, 1, 5]
def baseStart_296856 : Nat := 118140960795 + 296856 * 2 ^ 59
def prefixEnd_296856 : Nat := 4983230072969 + 3 ^ 40 * 296856 * 2
def baseEnd_296856 : Nat := 45164389087761713551049

theorem tailTrace_296856 : CollatzResearch.WordTrace tailWord_296856 prefixEnd_296856 45164389087761713551049 := by
  unfold tailWord_296856
  simp only [CollatzResearch.WordTrace]
  refine ⟨5413613906274442906779211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7218151875032590542372281 5413613906274442906779211)
  ·
    refine ⟨8120420859411664360168817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5413613906274442906779211 8120420859411664360168817)
    ·
      refine ⟨6090315644558748270126613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8120420859411664360168817 6090315644558748270126613)
      ·
        refine ⟨285483545838691325162185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6090315644558748270126613 285483545838691325162185)
        ·
          refine ⟨214112659379018493871639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285483545838691325162185 214112659379018493871639)
          ·
            refine ⟨321168989068527740807459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214112659379018493871639 321168989068527740807459)
            ·
              refine ⟨481753483602791611211189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321168989068527740807459 481753483602791611211189)
              ·
                refine ⟨45164389087761713551049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 481753483602791611211189 45164389087761713551049)
                ·
                  rfl

theorem cell20_296856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_296856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296856 prefixEnd_296856 := by exact prefixLift 296856
  have htrace : WordTrace (prefixWord ++ tailWord_296856) baseStart_296856 baseEnd_296856 := by
    simpa [prefixWord, tailWord_296856, baseEnd_296856] using wordTrace_append hprefix tailTrace_296856
  have hstable : (prefixWord ++ tailWord_296856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296856).length < 2 ^ (prefixWord ++ tailWord_296856).sum := by decide
  have hdescent : baseEnd_296856 < baseStart_296856 := by decide
  rcases family_descends (prefixWord ++ tailWord_296856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296860 : List Nat := [2, 2, 3, 3, 1, 1, 3, 5]
def baseStart_296860 : Nat := 118140960795 + 296860 * 2 ^ 59
def prefixEnd_296860 : Nat := 4983230072969 + 3 ^ 40 * 296860 * 2
def baseEnd_296860 : Nat := 45164997657426301506599

theorem tailTrace_296860 : CollatzResearch.WordTrace tailWord_296860 prefixEnd_296860 45164997657426301506599 := by
  unfold tailWord_296860
  simp only [CollatzResearch.WordTrace]
  refine ⟨5413686852267197248352017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7218249136356262997802689 5413686852267197248352017)
  ·
    refine ⟨4060265139200397936264013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5413686852267197248352017 4060265139200397936264013)
    ·
      refine ⟨1522599427200149226099005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4060265139200397936264013 1522599427200149226099005)
      ·
        refine ⟨570974785200055959787127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1522599427200149226099005 570974785200055959787127)
        ·
          refine ⟨856462177800083939680691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570974785200055959787127 856462177800083939680691)
          ·
            refine ⟨1284693266700125909521037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856462177800083939680691 1284693266700125909521037)
            ·
              refine ⟨481759975012547216070389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1284693266700125909521037 481759975012547216070389)
              ·
                refine ⟨45164997657426301506599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 481759975012547216070389 45164997657426301506599)
                ·
                  rfl

theorem cell20_296860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_296860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296860 prefixEnd_296860 := by exact prefixLift 296860
  have htrace : WordTrace (prefixWord ++ tailWord_296860) baseStart_296860 baseEnd_296860 := by
    simpa [prefixWord, tailWord_296860, baseEnd_296860] using wordTrace_append hprefix tailTrace_296860
  have hstable : (prefixWord ++ tailWord_296860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296860).length < 2 ^ (prefixWord ++ tailWord_296860).sum := by decide
  have hdescent : baseEnd_296860 < baseStart_296860 := by decide
  rcases family_descends (prefixWord ++ tailWord_296860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296888 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 5]
def baseStart_296888 : Nat := 118140960795 + 296888 * 2 ^ 59
def prefixEnd_296888 : Nat := 4983230072969 + 3 ^ 40 * 296888 * 2
def baseEnd_296888 : Nat := 135507772935235251586349

theorem tailTrace_296888 : CollatzResearch.WordTrace tailWord_296888 prefixEnd_296888 135507772935235251586349 := by
  unfold tailWord_296888
  simp only [CollatzResearch.WordTrace]
  refine ⟨5414197474216477639361659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7218929965621970185815545 5414197474216477639361659)
  ·
    refine ⟨8121296211324716459042489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5414197474216477639361659 8121296211324716459042489)
    ·
      refine ⟨6090972158493537344281867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8121296211324716459042489 6090972158493537344281867)
      ·
        refine ⟨9136458237740306016422801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6090972158493537344281867 9136458237740306016422801)
        ·
          refine ⟨6852343678305229512317101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9136458237740306016422801 6852343678305229512317101)
          ·
            refine ⟨2569628879364461067118913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6852343678305229512317101 2569628879364461067118913)
            ·
              refine ⟨1927221659523345800339185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2569628879364461067118913 1927221659523345800339185)
              ·
                refine ⟨1445416244642509350254389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1927221659523345800339185 1445416244642509350254389)
                ·
                  refine ⟨135507772935235251586349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1445416244642509350254389 135507772935235251586349)
                  ·
                    rfl

theorem cell20_296888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_296888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296888 prefixEnd_296888 := by exact prefixLift 296888
  have htrace : WordTrace (prefixWord ++ tailWord_296888) baseStart_296888 baseEnd_296888 := by
    simpa [prefixWord, tailWord_296888, baseEnd_296888] using wordTrace_append hprefix tailTrace_296888
  have hstable : (prefixWord ++ tailWord_296888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296888).length < 2 ^ (prefixWord ++ tailWord_296888).sum := by decide
  have hdescent : baseEnd_296888 < baseStart_296888 := by decide
  rcases family_descends (prefixWord ++ tailWord_296888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296895 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 6]
def baseStart_296895 : Nat := 118140960795 + 296895 * 2 ^ 59
def prefixEnd_296895 : Nat := 4983230072969 + 3 ^ 40 * 296895 * 2
def baseEnd_296895 : Nat := 135510967925974338352987

theorem tailTrace_296895 : CollatzResearch.WordTrace tailWord_296895 prefixEnd_296895 135510967925974338352987 := by
  unfold tailWord_296895
  simp only [CollatzResearch.WordTrace]
  refine ⟨10828650259407595474228139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7219100172938396982818759 10828650259407595474228139)
  ·
    refine ⟨16242975389111393211342209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10828650259407595474228139 16242975389111393211342209)
    ·
      refine ⟨12182231541833544908506657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16242975389111393211342209 12182231541833544908506657)
      ·
        refine ⟨9136673656375158681379993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12182231541833544908506657 9136673656375158681379993)
        ·
          refine ⟨6852505242281369011034995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9136673656375158681379993 6852505242281369011034995)
          ·
            refine ⟨10278757863422053516552493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6852505242281369011034995 10278757863422053516552493)
            ·
              refine ⟨3854534198783270068707185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10278757863422053516552493 3854534198783270068707185)
              ·
                refine ⟨2890900649087452551530389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3854534198783270068707185 2890900649087452551530389)
                ·
                  refine ⟨135510967925974338352987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2890900649087452551530389 135510967925974338352987)
                  ·
                    rfl

theorem cell20_296895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_296895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296895 prefixEnd_296895 := by exact prefixLift 296895
  have htrace : WordTrace (prefixWord ++ tailWord_296895) baseStart_296895 baseEnd_296895 := by
    simpa [prefixWord, tailWord_296895, baseEnd_296895] using wordTrace_append hprefix tailTrace_296895
  have hstable : (prefixWord ++ tailWord_296895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296895).length < 2 ^ (prefixWord ++ tailWord_296895).sum := by decide
  have hdescent : baseEnd_296895 < baseStart_296895 := by decide
  rcases family_descends (prefixWord ++ tailWord_296895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296918 : List Nat := [5, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_296918 : Nat := 118140960795 + 296918 * 2 ^ 59
def prefixEnd_296918 : Nat := 4983230072969 + 3 ^ 40 * 296918 * 2
def baseEnd_296918 : Nat := 135521465752688480586227

theorem tailTrace_296918 : CollatzResearch.WordTrace tailWord_296918 prefixEnd_296918 135521465752688480586227 := by
  unfold tailWord_296918
  simp only [CollatzResearch.WordTrace]
  refine ⟨676843071145266900144713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7219659425549513601543605 676843071145266900144713)
  ·
    refine ⟨507632303358950175108535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 676843071145266900144713 507632303358950175108535)
    ·
      refine ⟨761448455038425262662803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 507632303358950175108535 761448455038425262662803)
      ·
        refine ⟨1142172682557637893994205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 761448455038425262662803 1142172682557637893994205)
        ·
          refine ⟨428314755959114210247827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1142172682557637893994205 428314755959114210247827)
          ·
            refine ⟨642472133938671315371741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428314755959114210247827 642472133938671315371741)
            ·
              refine ⟨240927050227001743264403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 642472133938671315371741 240927050227001743264403)
              ·
                refine ⟨361390575340502614896605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240927050227001743264403 361390575340502614896605)
                ·
                  refine ⟨135521465752688480586227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361390575340502614896605 135521465752688480586227)
                  ·
                    rfl

theorem cell20_296918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_296918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296918 prefixEnd_296918 := by exact prefixLift 296918
  have htrace : WordTrace (prefixWord ++ tailWord_296918) baseStart_296918 baseEnd_296918 := by
    simpa [prefixWord, tailWord_296918, baseEnd_296918] using wordTrace_append hprefix tailTrace_296918
  have hstable : (prefixWord ++ tailWord_296918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296918).length < 2 ^ (prefixWord ++ tailWord_296918).sum := by decide
  have hdescent : baseEnd_296918 < baseStart_296918 := by decide
  rcases family_descends (prefixWord ++ tailWord_296918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296967 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 4]
def baseStart_296967 : Nat := 118140960795 + 296967 * 2 ^ 59
def prefixEnd_296967 : Nat := 4983230072969 + 3 ^ 40 * 296967 * 2
def baseEnd_296967 : Nat := 135543830687862087952693

theorem tailTrace_296967 : CollatzResearch.WordTrace tailWord_296967 prefixEnd_296967 135543830687862087952693 := by
  unfold tailWord_296967
  simp only [CollatzResearch.WordTrace]
  refine ⟨10831276315146751770849155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7220850876764501180566103 10831276315146751770849155)
  ·
    refine ⟨16246914472720127656273733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10831276315146751770849155 16246914472720127656273733)
    ·
      refine ⟨3046296463635023935551325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16246914472720127656273733 3046296463635023935551325)
      ·
        refine ⟨1142361173863133975831747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3046296463635023935551325 1142361173863133975831747)
        ·
          refine ⟨1713541760794700963747621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1142361173863133975831747 1713541760794700963747621)
          ·
            refine ⟨321289080149006430702679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1713541760794700963747621 321289080149006430702679)
            ·
              refine ⟨481933620223509646054019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321289080149006430702679 481933620223509646054019)
              ·
                refine ⟨722900430335264469081029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481933620223509646054019 722900430335264469081029)
                ·
                  refine ⟨135543830687862087952693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 722900430335264469081029 135543830687862087952693)
                  ·
                    rfl

theorem cell20_296967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 4].length) (baseStart_296967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_296967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_296967 prefixEnd_296967 := by exact prefixLift 296967
  have htrace : WordTrace (prefixWord ++ tailWord_296967) baseStart_296967 baseEnd_296967 := by
    simpa [prefixWord, tailWord_296967, baseEnd_296967] using wordTrace_append hprefix tailTrace_296967
  have hstable : (prefixWord ++ tailWord_296967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296967).length < 2 ^ (prefixWord ++ tailWord_296967).sum := by decide
  have hdescent : baseEnd_296967 < baseStart_296967 := by decide
  rcases family_descends (prefixWord ++ tailWord_296967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297012 : List Nat := [2, 5, 1, 2, 2, 8]
def baseStart_297012 : Nat := 118140960795 + 297012 * 2 ^ 59
def prefixEnd_297012 : Nat := 4983230072969 + 3 ^ 40 * 297012 * 2
def baseEnd_297012 : Nat := 5020902589408960424167

theorem tailTrace_297012 : CollatzResearch.WordTrace tailWord_297012 prefixEnd_297012 5020902589408960424167 := by
  unfold tailWord_297012
  simp only [CollatzResearch.WordTrace]
  refine ⟨5416458799991862228118645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7221945066655816304158193 5416458799991862228118645)
  ·
    refine ⟨507793012499237083886123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5416458799991862228118645 507793012499237083886123)
    ·
      refine ⟨761689518748855625829185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 507793012499237083886123 761689518748855625829185)
      ·
        refine ⟨571267139061641719371889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 761689518748855625829185 571267139061641719371889)
        ·
          refine ⟨428450354296231289528917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 571267139061641719371889 428450354296231289528917)
          ·
            refine ⟨5020902589408960424167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 428450354296231289528917 5020902589408960424167)
            ·
              rfl

theorem cell20_297012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 8].length) (baseStart_297012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297012 prefixEnd_297012 := by exact prefixLift 297012
  have htrace : WordTrace (prefixWord ++ tailWord_297012) baseStart_297012 baseEnd_297012 := by
    simpa [prefixWord, tailWord_297012, baseEnd_297012] using wordTrace_append hprefix tailTrace_297012
  have hstable : (prefixWord ++ tailWord_297012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297012).length < 2 ^ (prefixWord ++ tailWord_297012).sum := by decide
  have hdescent : baseEnd_297012 < baseStart_297012 := by decide
  rcases family_descends (prefixWord ++ tailWord_297012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297016 : List Nat := [2, 1, 2, 1, 14]
def baseStart_297016 : Nat := 118140960795 + 297016 * 2 ^ 59
def prefixEnd_297016 : Nat := 4983230072969 + 3 ^ 40 * 297016 * 2
def baseEnd_297016 : Nat := 1673656736086860436039

theorem tailTrace_297016 : CollatzResearch.WordTrace tailWord_297016 prefixEnd_297016 1673656736086860436039 := by
  unfold tailWord_297016
  simp only [CollatzResearch.WordTrace]
  refine ⟨5416531745984616569691451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7222042327979488759588601 5416531745984616569691451)
  ·
    refine ⟨8124797618976924854537177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5416531745984616569691451 8124797618976924854537177)
    ·
      refine ⟨6093598214232693640902883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8124797618976924854537177 6093598214232693640902883)
      ·
        refine ⟨9140397321349040461354325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6093598214232693640902883 9140397321349040461354325)
        ·
          refine ⟨1673656736086860436039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 9140397321349040461354325 1673656736086860436039)
          ·
            rfl

theorem cell20_297016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 14].length) (baseStart_297016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297016 prefixEnd_297016 := by exact prefixLift 297016
  have htrace : WordTrace (prefixWord ++ tailWord_297016) baseStart_297016 baseEnd_297016 := by
    simpa [prefixWord, tailWord_297016, baseEnd_297016] using wordTrace_append hprefix tailTrace_297016
  have hstable : (prefixWord ++ tailWord_297016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297016).length < 2 ^ (prefixWord ++ tailWord_297016).sum := by decide
  have hdescent : baseEnd_297016 < baseStart_297016 := by decide
  rcases family_descends (prefixWord ++ tailWord_297016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297046 : List Nat := [5, 2, 2, 1, 1, 2, 3, 4]
def baseStart_297046 : Nat := 118140960795 + 297046 * 2 ^ 59
def prefixEnd_297046 : Nat := 4983230072969 + 3 ^ 40 * 297046 * 2
def baseEnd_297046 : Nat := 45193296146829641439679

theorem tailTrace_297046 : CollatzResearch.WordTrace tailWord_297046 prefixEnd_297046 45193296146829641439679 := by
  unfold tailWord_297046
  simp only [CollatzResearch.WordTrace]
  refine ⟨677134855116284266435937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7222771787907032175316661 677134855116284266435937)
  ·
    refine ⟨507851141337213199826953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 677134855116284266435937 507851141337213199826953)
    ·
      refine ⟨380888356002909899870215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 507851141337213199826953 380888356002909899870215)
      ·
        refine ⟨571332534004364849805323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380888356002909899870215 571332534004364849805323)
        ·
          refine ⟨856998801006547274707985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571332534004364849805323 856998801006547274707985)
          ·
            refine ⟨642749100754910456030989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 856998801006547274707985 642749100754910456030989)
            ·
              refine ⟨241030912783091421011621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 642749100754910456030989 241030912783091421011621)
              ·
                refine ⟨45193296146829641439679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241030912783091421011621 45193296146829641439679)
                ·
                  rfl

theorem cell20_297046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_297046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297046 prefixEnd_297046 := by exact prefixLift 297046
  have htrace : WordTrace (prefixWord ++ tailWord_297046) baseStart_297046 baseEnd_297046 := by
    simpa [prefixWord, tailWord_297046, baseEnd_297046] using wordTrace_append hprefix tailTrace_297046
  have hstable : (prefixWord ++ tailWord_297046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297046).length < 2 ^ (prefixWord ++ tailWord_297046).sum := by decide
  have hdescent : baseEnd_297046 < baseStart_297046 := by decide
  rcases family_descends (prefixWord ++ tailWord_297046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297047 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 6]
def baseStart_297047 : Nat := 118140960795 + 297047 * 2 ^ 59
def prefixEnd_297047 : Nat := 4983230072969 + 3 ^ 40 * 297047 * 2
def baseEnd_297047 : Nat := 135580344867737365285699

theorem tailTrace_297047 : CollatzResearch.WordTrace tailWord_297047 prefixEnd_297047 135580344867737365285699 := by
  unfold tailWord_297047
  simp only [CollatzResearch.WordTrace]
  refine ⟨10834194154856925433761395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7222796103237950289174263 10834194154856925433761395)
  ·
    refine ⟨16251291232285388150642093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10834194154856925433761395 16251291232285388150642093)
    ·
      refine ⟨6094234212107020556490785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16251291232285388150642093 6094234212107020556490785)
      ·
        refine ⟨4570675659080265417368089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6094234212107020556490785 4570675659080265417368089)
        ·
          refine ⟨3428006744310199063026067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4570675659080265417368089 3428006744310199063026067)
          ·
            refine ⟨5142010116465298594539101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3428006744310199063026067 5142010116465298594539101)
            ·
              refine ⟨1928253793674486972952163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5142010116465298594539101 1928253793674486972952163)
              ·
                refine ⟨2892380690511730459428245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1928253793674486972952163 2892380690511730459428245)
                ·
                  refine ⟨135580344867737365285699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2892380690511730459428245 135580344867737365285699)
                  ·
                    rfl

theorem cell20_297047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_297047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297047 prefixEnd_297047 := by exact prefixLift 297047
  have htrace : WordTrace (prefixWord ++ tailWord_297047) baseStart_297047 baseEnd_297047 := by
    simpa [prefixWord, tailWord_297047, baseEnd_297047] using wordTrace_append hprefix tailTrace_297047
  have hstable : (prefixWord ++ tailWord_297047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297047).length < 2 ^ (prefixWord ++ tailWord_297047).sum := by decide
  have hdescent : baseEnd_297047 < baseStart_297047 := by decide
  rcases family_descends (prefixWord ++ tailWord_297047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297074 : List Nat := [3, 2, 1, 2, 2, 4, 1, 2, 3]
def baseStart_297074 : Nat := 118140960795 + 297074 * 2 ^ 59
def prefixEnd_297074 : Nat := 4983230072969 + 3 ^ 40 * 297074 * 2
def baseEnd_297074 : Nat := 135592668403445271385589

theorem tailTrace_297074 : CollatzResearch.WordTrace tailWord_297074 prefixEnd_297074 135592668403445271385589 := by
  unfold tailWord_297074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2708794731439777261248569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7223452617172739363329517 2708794731439777261248569)
  ·
    refine ⟨2031596048579832945936427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2708794731439777261248569 2031596048579832945936427)
    ·
      refine ⟨3047394072869749418904641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2031596048579832945936427 3047394072869749418904641)
      ·
        refine ⟨2285545554652312064178481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3047394072869749418904641 2285545554652312064178481)
        ·
          refine ⟨1714159165989234048133861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2285545554652312064178481 1714159165989234048133861)
          ·
            refine ⟨321404843622981384025099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1714159165989234048133861 321404843622981384025099)
            ·
              refine ⟨482107265434472076037649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321404843622981384025099 482107265434472076037649)
              ·
                refine ⟨361580449075854057028237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482107265434472076037649 361580449075854057028237)
                ·
                  refine ⟨135592668403445271385589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361580449075854057028237 135592668403445271385589)
                  ·
                    rfl

theorem cell20_297074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_297074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297074 prefixEnd_297074 := by exact prefixLift 297074
  have htrace : WordTrace (prefixWord ++ tailWord_297074) baseStart_297074 baseEnd_297074 := by
    simpa [prefixWord, tailWord_297074, baseEnd_297074] using wordTrace_append hprefix tailTrace_297074
  have hstable : (prefixWord ++ tailWord_297074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297074).length < 2 ^ (prefixWord ++ tailWord_297074).sum := by decide
  have hdescent : baseEnd_297074 < baseStart_297074 := by decide
  rcases family_descends (prefixWord ++ tailWord_297074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297081 : List Nat := [1, 2, 1, 3, 4, 1, 2, 4, 2]
def baseStart_297081 : Nat := 118140960795 + 297081 * 2 ^ 59
def prefixEnd_297081 : Nat := 4983230072969 + 3 ^ 40 * 297081 * 2
def baseEnd_297081 : Nat := 135595863394184358152227

theorem tailTrace_297081 : CollatzResearch.WordTrace tailWord_297081 prefixEnd_297081 135595863394184358152227 := by
  unfold tailWord_297081
  simp only [CollatzResearch.WordTrace]
  refine ⟨10835434236733749240499097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7223622824489166160332731 10835434236733749240499097)
  ·
    refine ⟨8126575677550311930374323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10835434236733749240499097 8126575677550311930374323)
    ·
      refine ⟨12189863516325467895561485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8126575677550311930374323 12189863516325467895561485)
      ·
        refine ⟨4571198818622050460835557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12189863516325467895561485 4571198818622050460835557)
        ·
          refine ⟨857099778491634461406667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4571198818622050460835557 857099778491634461406667)
          ·
            refine ⟨1285649667737451692110001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857099778491634461406667 1285649667737451692110001)
            ·
              refine ⟨964237250803088769082501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1285649667737451692110001 964237250803088769082501)
              ·
                refine ⟨180794484525579144202969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 964237250803088769082501 180794484525579144202969)
                ·
                  refine ⟨135595863394184358152227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180794484525579144202969 135595863394184358152227)
                  ·
                    rfl

theorem cell20_297081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 4, 2].length) (baseStart_297081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297081 prefixEnd_297081 := by exact prefixLift 297081
  have htrace : WordTrace (prefixWord ++ tailWord_297081) baseStart_297081 baseEnd_297081 := by
    simpa [prefixWord, tailWord_297081, baseEnd_297081] using wordTrace_append hprefix tailTrace_297081
  have hstable : (prefixWord ++ tailWord_297081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297081).length < 2 ^ (prefixWord ++ tailWord_297081).sum := by decide
  have hdescent : baseEnd_297081 < baseStart_297081 := by decide
  rcases family_descends (prefixWord ++ tailWord_297081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297116 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 7]
def baseStart_297116 : Nat := 118140960795 + 297116 * 2 ^ 59
def prefixEnd_297116 : Nat := 4983230072969 + 3 ^ 40 * 297116 * 2
def baseEnd_297116 : Nat := 135611838347879791985417

theorem tailTrace_297116 : CollatzResearch.WordTrace tailWord_297116 prefixEnd_297116 135611838347879791985417 := by
  unfold tailWord_297116
  simp only [CollatzResearch.WordTrace]
  refine ⟨5418355395803475109011601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7224473861071300145348801 5418355395803475109011601)
  ·
    refine ⟨4063766546852606331758701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5418355395803475109011601 4063766546852606331758701)
    ·
      refine ⟨1523912455069727374409513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4063766546852606331758701 1523912455069727374409513)
      ·
        refine ⟨1142934341302295530807135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1523912455069727374409513 1142934341302295530807135)
        ·
          refine ⟨1714401511953443296210703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1142934341302295530807135 1714401511953443296210703)
          ·
            refine ⟨2571602267930164944316055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714401511953443296210703 2571602267930164944316055)
            ·
              refine ⟨3857403401895247416474083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571602267930164944316055 3857403401895247416474083)
              ·
                refine ⟨5786105102842871124711125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3857403401895247416474083 5786105102842871124711125)
                ·
                  refine ⟨135611838347879791985417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5786105102842871124711125 135611838347879791985417)
                  ·
                    rfl

theorem cell20_297116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_297116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297116 prefixEnd_297116 := by exact prefixLift 297116
  have htrace : WordTrace (prefixWord ++ tailWord_297116) baseStart_297116 baseEnd_297116 := by
    simpa [prefixWord, tailWord_297116, baseEnd_297116] using wordTrace_append hprefix tailTrace_297116
  have hstable : (prefixWord ++ tailWord_297116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297116).length < 2 ^ (prefixWord ++ tailWord_297116).sum := by decide
  have hdescent : baseEnd_297116 < baseStart_297116 := by decide
  rcases family_descends (prefixWord ++ tailWord_297116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297133 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 5]
def baseStart_297133 : Nat := 118140960795 + 297133 * 2 ^ 59
def prefixEnd_297133 : Nat := 4983230072969 + 3 ^ 40 * 297133 * 2
def baseEnd_297133 : Nat := 135619597611103288418681

theorem tailTrace_297133 : CollatzResearch.WordTrace tailWord_297133 prefixEnd_297133 135619597611103288418681 := by
  unfold tailWord_297133
  simp only [CollatzResearch.WordTrace]
  refine ⟨10837330832545362121392053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7224887221696908080928035 10837330832545362121392053)
  ·
    refine ⟨1015999765551127698880505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10837330832545362121392053 1015999765551127698880505)
    ·
      refine ⟨761999824163345774160379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1015999765551127698880505 761999824163345774160379)
      ·
        refine ⟨1142999736245018661240569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 761999824163345774160379 1142999736245018661240569)
        ·
          refine ⟨857249802183763995930427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1142999736245018661240569 857249802183763995930427)
          ·
            refine ⟨1285874703275645993895641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857249802183763995930427 1285874703275645993895641)
            ·
              refine ⟨964406027456734495421731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1285874703275645993895641 964406027456734495421731)
              ·
                refine ⟨1446609041185101743132597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 964406027456734495421731 1446609041185101743132597)
                ·
                  refine ⟨135619597611103288418681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1446609041185101743132597 135619597611103288418681)
                  ·
                    rfl

theorem cell20_297133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_297133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297133 prefixEnd_297133 := by exact prefixLift 297133
  have htrace : WordTrace (prefixWord ++ tailWord_297133) baseStart_297133 baseEnd_297133 := by
    simpa [prefixWord, tailWord_297133, baseEnd_297133] using wordTrace_append hprefix tailTrace_297133
  have hstable : (prefixWord ++ tailWord_297133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297133).length < 2 ^ (prefixWord ++ tailWord_297133).sum := by decide
  have hdescent : baseEnd_297133 < baseStart_297133 := by decide
  rcases family_descends (prefixWord ++ tailWord_297133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297150 : List Nat := [4, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_297150 : Nat := 118140960795 + 297150 * 2 ^ 59
def prefixEnd_297150 : Nat := 4983230072969 + 3 ^ 40 * 297150 * 2
def baseEnd_297150 : Nat := 135627356874326784851945

theorem tailTrace_297150 : CollatzResearch.WordTrace tailWord_297150 prefixEnd_297150 135627356874326784851945 := by
  unfold tailWord_297150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354743859185471753095113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7225300582322516016507269 1354743859185471753095113)
  ·
    refine ⟨1016057894389103814821335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1354743859185471753095113 1016057894389103814821335)
    ·
      refine ⟨1524086841583655722232003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1016057894389103814821335 1524086841583655722232003)
      ·
        refine ⟨2286130262375483583348005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1524086841583655722232003 2286130262375483583348005)
        ·
          refine ⟨428649424195403171877751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2286130262375483583348005 428649424195403171877751)
          ·
            refine ⟨642974136293104757816627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428649424195403171877751 642974136293104757816627)
            ·
              refine ⟨964461204439657136724941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642974136293104757816627 964461204439657136724941)
              ·
                refine ⟨361672951664871426271853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 964461204439657136724941 361672951664871426271853)
                ·
                  refine ⟨135627356874326784851945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361672951664871426271853 135627356874326784851945)
                  ·
                    rfl

theorem cell20_297150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_297150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297150 prefixEnd_297150 := by exact prefixLift 297150
  have htrace : WordTrace (prefixWord ++ tailWord_297150) baseStart_297150 baseEnd_297150 := by
    simpa [prefixWord, tailWord_297150, baseEnd_297150] using wordTrace_append hprefix tailTrace_297150
  have hstable : (prefixWord ++ tailWord_297150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297150).length < 2 ^ (prefixWord ++ tailWord_297150).sum := by decide
  have hdescent : baseEnd_297150 < baseStart_297150 := by decide
  rcases family_descends (prefixWord ++ tailWord_297150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297191 : List Nat := [1, 1, 5, 3, 1, 3, 2, 2, 2]
def baseStart_297191 : Nat := 118140960795 + 297191 * 2 ^ 59
def prefixEnd_297191 : Nat := 4983230072969 + 3 ^ 40 * 297191 * 2
def baseEnd_297191 : Nat := 135646070391512864485111

theorem tailTrace_297191 : CollatzResearch.WordTrace tailWord_297191 prefixEnd_297191 135646070391512864485111 := by
  unfold tailWord_297191
  simp only [CollatzResearch.WordTrace]
  refine ⟨10839446266335238027003427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7226297510890158684668951 10839446266335238027003427)
  ·
    refine ⟨16259169399502857040505141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10839446266335238027003427 16259169399502857040505141)
    ·
      refine ⟨1524297131203392847547357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16259169399502857040505141 1524297131203392847547357)
      ·
        refine ⟨571611424201272317830259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1524297131203392847547357 571611424201272317830259)
        ·
          refine ⟨857417136301908476745389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571611424201272317830259 857417136301908476745389)
          ·
            refine ⟨321531426113215678779521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 857417136301908476745389 321531426113215678779521)
            ·
              refine ⟨241148569584911759084641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321531426113215678779521 241148569584911759084641)
              ·
                refine ⟨180861427188683819313481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241148569584911759084641 180861427188683819313481)
                ·
                  refine ⟨135646070391512864485111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180861427188683819313481 135646070391512864485111)
                  ·
                    rfl

theorem cell20_297191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 2, 2].length) (baseStart_297191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297191 prefixEnd_297191 := by exact prefixLift 297191
  have htrace : WordTrace (prefixWord ++ tailWord_297191) baseStart_297191 baseEnd_297191 := by
    simpa [prefixWord, tailWord_297191, baseEnd_297191] using wordTrace_append hprefix tailTrace_297191
  have hstable : (prefixWord ++ tailWord_297191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297191).length < 2 ^ (prefixWord ++ tailWord_297191).sum := by decide
  have hdescent : baseEnd_297191 < baseStart_297191 := by decide
  rcases family_descends (prefixWord ++ tailWord_297191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297202 : List Nat := [3, 2, 1, 3, 2, 3, 1, 5]
def baseStart_297202 : Nat := 118140960795 + 297202 * 2 ^ 59
def prefixEnd_297202 : Nat := 4983230072969 + 3 ^ 40 * 297202 * 2
def baseEnd_297202 : Nat := 45217030363748571706133

theorem tailTrace_297202 : CollatzResearch.WordTrace tailWord_297202 prefixEnd_297202 45217030363748571706133 := by
  unfold tailWord_297202
  simp only [CollatzResearch.WordTrace]
  refine ⟨2709961867323846726413465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7226564979530257937102573 2709961867323846726413465)
  ·
    refine ⟨2032471400492885044810099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2709961867323846726413465 2032471400492885044810099)
    ·
      refine ⟨3048707100739327567215149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2032471400492885044810099 3048707100739327567215149)
      ·
        refine ⟨1143265162777247837705681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3048707100739327567215149 1143265162777247837705681)
        ·
          refine ⟨857448872082935878279261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1143265162777247837705681 857448872082935878279261)
          ·
            refine ⟨321543327031100954354723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 857448872082935878279261 321543327031100954354723)
            ·
              refine ⟨482314990546651431532085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321543327031100954354723 482314990546651431532085)
              ·
                refine ⟨45217030363748571706133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 482314990546651431532085 45217030363748571706133)
                ·
                  rfl

theorem cell20_297202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_297202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297202 prefixEnd_297202 := by exact prefixLift 297202
  have htrace : WordTrace (prefixWord ++ tailWord_297202) baseStart_297202 baseEnd_297202 := by
    simpa [prefixWord, tailWord_297202, baseEnd_297202] using wordTrace_append hprefix tailTrace_297202
  have hstable : (prefixWord ++ tailWord_297202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297202).length < 2 ^ (prefixWord ++ tailWord_297202).sum := by decide
  have hdescent : baseEnd_297202 < baseStart_297202 := by decide
  rcases family_descends (prefixWord ++ tailWord_297202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297230 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_297230 : Nat := 118140960795 + 297230 * 2 ^ 59
def prefixEnd_297230 : Nat := 4983230072969 + 3 ^ 40 * 297230 * 2
def baseEnd_297230 : Nat := 135663871054202062184951

theorem tailTrace_297230 : CollatzResearch.WordTrace tailWord_297230 prefixEnd_297230 135663871054202062184951 := by
  unfold tailWord_297230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1355108589149243460959143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7227245808795965125115429 1355108589149243460959143)
  ·
    refine ⟨2032662883723865191438715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1355108589149243460959143 2032662883723865191438715)
    ·
      refine ⟨3048994325585797787158073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2032662883723865191438715 3048994325585797787158073)
      ·
        refine ⟨2286745744189348340368555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3048994325585797787158073 2286745744189348340368555)
        ·
          refine ⟨3430118616284022510552833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2286745744189348340368555 3430118616284022510552833)
          ·
            refine ⟨2572588962213016882914625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3430118616284022510552833 2572588962213016882914625)
            ·
              refine ⟨1929441721659762662185969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2572588962213016882914625 1929441721659762662185969)
              ·
                refine ⟨1447081291244821996639477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1929441721659762662185969 1447081291244821996639477)
                ·
                  refine ⟨135663871054202062184951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1447081291244821996639477 135663871054202062184951)
                  ·
                    rfl

theorem cell20_297230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_297230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297230 prefixEnd_297230 := by exact prefixLift 297230
  have htrace : WordTrace (prefixWord ++ tailWord_297230) baseStart_297230 baseEnd_297230 := by
    simpa [prefixWord, tailWord_297230, baseEnd_297230] using wordTrace_append hprefix tailTrace_297230
  have hstable : (prefixWord ++ tailWord_297230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297230).length < 2 ^ (prefixWord ++ tailWord_297230).sum := by decide
  have hdescent : baseEnd_297230 < baseStart_297230 := by decide
  rcases family_descends (prefixWord ++ tailWord_297230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297233 : List Nat := [1, 2, 2, 1, 1, 6, 2, 3, 2]
def baseStart_297233 : Nat := 118140960795 + 297233 * 2 ^ 59
def prefixEnd_297233 : Nat := 4983230072969 + 3 ^ 40 * 297233 * 2
def baseEnd_297233 : Nat := 135665240335947385084939

theorem tailTrace_297233 : CollatzResearch.WordTrace tailWord_297233 prefixEnd_297233 135665240335947385084939 := by
  unfold tailWord_297233
  simp only [CollatzResearch.WordTrace]
  refine ⟨10840978132183079200032353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7227318754788719466688235 10840978132183079200032353)
  ·
    refine ⟨8130733599137309400024265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10840978132183079200032353 8130733599137309400024265)
    ·
      refine ⟨6098050199352982050018199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8130733599137309400024265 6098050199352982050018199)
      ·
        refine ⟨9147075299029473075027299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6098050199352982050018199 9147075299029473075027299)
        ·
          refine ⟨13720612948544209612540949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9147075299029473075027299 13720612948544209612540949)
          ·
            refine ⟨643153731963009825587857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13720612948544209612540949 643153731963009825587857)
            ·
              refine ⟨482365298972257369190893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643153731963009825587857 482365298972257369190893)
              ·
                refine ⟨180886987114596513446585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 482365298972257369190893 180886987114596513446585)
                ·
                  refine ⟨135665240335947385084939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180886987114596513446585 135665240335947385084939)
                  ·
                    rfl

theorem cell20_297233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 2].length) (baseStart_297233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297233 prefixEnd_297233 := by exact prefixLift 297233
  have htrace : WordTrace (prefixWord ++ tailWord_297233) baseStart_297233 baseEnd_297233 := by
    simpa [prefixWord, tailWord_297233, baseEnd_297233] using wordTrace_append hprefix tailTrace_297233
  have hstable : (prefixWord ++ tailWord_297233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297233).length < 2 ^ (prefixWord ++ tailWord_297233).sum := by decide
  have hdescent : baseEnd_297233 < baseStart_297233 := by decide
  rcases family_descends (prefixWord ++ tailWord_297233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297247 : List Nat := [1, 1, 2, 4, 3, 1, 3, 2, 3]
def baseStart_297247 : Nat := 118140960795 + 297247 * 2 ^ 59
def prefixEnd_297247 : Nat := 4983230072969 + 3 ^ 40 * 297247 * 2
def baseEnd_297247 : Nat := 135671630317425558618215

theorem tailTrace_297247 : CollatzResearch.WordTrace tailWord_297247 prefixEnd_297247 135671630317425558618215 := by
  unfold tailWord_297247
  simp only [CollatzResearch.WordTrace]
  refine ⟨10841488754132359591041995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7227659169421573060694663 10841488754132359591041995)
  ·
    refine ⟨16262233131198539386562993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10841488754132359591041995 16262233131198539386562993)
    ·
      refine ⟨12196674848398904539922245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16262233131198539386562993 12196674848398904539922245)
      ·
        refine ⟨2286876534074794601235421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12196674848398904539922245 2286876534074794601235421)
        ·
          refine ⟨857578700278047975463283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2286876534074794601235421 857578700278047975463283)
          ·
            refine ⟨1286368050417071963194925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857578700278047975463283 1286368050417071963194925)
            ·
              refine ⟨482388018906401986198097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1286368050417071963194925 482388018906401986198097)
              ·
                refine ⟨361791014179801489648573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482388018906401986198097 361791014179801489648573)
                ·
                  refine ⟨135671630317425558618215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361791014179801489648573 135671630317425558618215)
                  ·
                    rfl

theorem cell20_297247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 3].length) (baseStart_297247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297247 prefixEnd_297247 := by exact prefixLift 297247
  have htrace : WordTrace (prefixWord ++ tailWord_297247) baseStart_297247 baseEnd_297247 := by
    simpa [prefixWord, tailWord_297247, baseEnd_297247] using wordTrace_append hprefix tailTrace_297247
  have hstable : (prefixWord ++ tailWord_297247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297247).length < 2 ^ (prefixWord ++ tailWord_297247).sum := by decide
  have hdescent : baseEnd_297247 < baseStart_297247 := by decide
  rcases family_descends (prefixWord ++ tailWord_297247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297278 : List Nat := [4, 2, 1, 2, 1, 2, 4, 4]
def baseStart_297278 : Nat := 118140960795 + 297278 * 2 ^ 59
def prefixEnd_297278 : Nat := 4983230072969 + 3 ^ 40 * 297278 * 2
def baseEnd_297278 : Nat := 45228593187375742861585

theorem tailTrace_297278 : CollatzResearch.WordTrace tailWord_297278 prefixEnd_297278 45228593187375742861585 := by
  unfold tailWord_297278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1355327427127506485677561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7228412944680034590280325 1355327427127506485677561)
  ·
    refine ⟨1016495570345629864258171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1355327427127506485677561 1016495570345629864258171)
    ·
      refine ⟨1524743355518444796387257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1016495570345629864258171 1524743355518444796387257)
      ·
        refine ⟨1143557516638833597290443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1524743355518444796387257 1143557516638833597290443)
        ·
          refine ⟨1715336274958250395935665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1143557516638833597290443 1715336274958250395935665)
          ·
            refine ⟨1286502206218687796951749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1715336274958250395935665 1286502206218687796951749)
            ·
              refine ⟨241219163666003961928453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1286502206218687796951749 241219163666003961928453)
              ·
                refine ⟨45228593187375742861585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241219163666003961928453 45228593187375742861585)
                ·
                  rfl

theorem cell20_297278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_297278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297278 prefixEnd_297278 := by exact prefixLift 297278
  have htrace : WordTrace (prefixWord ++ tailWord_297278) baseStart_297278 baseEnd_297278 := by
    simpa [prefixWord, tailWord_297278, baseEnd_297278] using wordTrace_append hprefix tailTrace_297278
  have hstable : (prefixWord ++ tailWord_297278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297278).length < 2 ^ (prefixWord ++ tailWord_297278).sum := by decide
  have hdescent : baseEnd_297278 < baseStart_297278 := by decide
  rcases family_descends (prefixWord ++ tailWord_297278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297284 : List Nat := [2, 3, 4, 1, 3, 1, 1, 3, 2]
def baseStart_297284 : Nat := 118140960795 + 297284 * 2 ^ 59
def prefixEnd_297284 : Nat := 4983230072969 + 3 ^ 40 * 297284 * 2
def baseEnd_297284 : Nat := 135688518125617874384731

theorem tailTrace_297284 : CollatzResearch.WordTrace tailWord_297284 prefixEnd_297284 135688518125617874384731 := by
  unfold tailWord_297284
  simp only [CollatzResearch.WordTrace]
  refine ⟨5421419127499157455069453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7228558836665543273425937 5421419127499157455069453)
  ·
    refine ⟨2033032172812184045651045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5421419127499157455069453 2033032172812184045651045)
    ·
      refine ⟨381193532402284508559571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2033032172812184045651045 381193532402284508559571)
      ·
        refine ⟨571790298603426762839357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381193532402284508559571 571790298603426762839357)
        ·
          refine ⟨214421361976285036064759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 571790298603426762839357 214421361976285036064759)
          ·
            refine ⟨321632042964427554097139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214421361976285036064759 321632042964427554097139)
            ·
              refine ⟨482448064446641331145709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321632042964427554097139 482448064446641331145709)
              ·
                refine ⟨180918024167490499179641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 482448064446641331145709 180918024167490499179641)
                ·
                  refine ⟨135688518125617874384731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180918024167490499179641 135688518125617874384731)
                  ·
                    rfl

theorem cell20_297284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_297284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297284 prefixEnd_297284 := by exact prefixLift 297284
  have htrace : WordTrace (prefixWord ++ tailWord_297284) baseStart_297284 baseEnd_297284 := by
    simpa [prefixWord, tailWord_297284, baseEnd_297284] using wordTrace_append hprefix tailTrace_297284
  have hstable : (prefixWord ++ tailWord_297284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297284).length < 2 ^ (prefixWord ++ tailWord_297284).sum := by decide
  have hdescent : baseEnd_297284 < baseStart_297284 := by decide
  rcases family_descends (prefixWord ++ tailWord_297284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297306 : List Nat := [3, 1, 1, 2, 1, 2, 1, 6, 3]
def baseStart_297306 : Nat := 118140960795 + 297306 * 2 ^ 59
def prefixEnd_297306 : Nat := 4983230072969 + 3 ^ 40 * 297306 * 2
def baseEnd_297306 : Nat := 135698559525083575651307

theorem tailTrace_297306 : CollatzResearch.WordTrace tailWord_297306 prefixEnd_297306 135698559525083575651307 := by
  unfold tailWord_297306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2710910165229653166859943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7229093773945741778293181 2710910165229653166859943)
  ·
    refine ⟨4066365247844479750289915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2710910165229653166859943 4066365247844479750289915)
    ·
      refine ⟨6099547871766719625434873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4066365247844479750289915 6099547871766719625434873)
      ·
        refine ⟨4574660903825039719076155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6099547871766719625434873 4574660903825039719076155)
        ·
          refine ⟨6861991355737559578614233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4574660903825039719076155 6861991355737559578614233)
          ·
            refine ⟨5146493516803169683960675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6861991355737559578614233 5146493516803169683960675)
            ·
              refine ⟨7719740275204754525941013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5146493516803169683960675 7719740275204754525941013)
              ·
                refine ⟨361862825400222868403485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7719740275204754525941013 361862825400222868403485)
                ·
                  refine ⟨135698559525083575651307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361862825400222868403485 135698559525083575651307)
                  ·
                    rfl

theorem cell20_297306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_297306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297306 prefixEnd_297306 := by exact prefixLift 297306
  have htrace : WordTrace (prefixWord ++ tailWord_297306) baseStart_297306 baseEnd_297306 := by
    simpa [prefixWord, tailWord_297306, baseEnd_297306] using wordTrace_append hprefix tailTrace_297306
  have hstable : (prefixWord ++ tailWord_297306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297306).length < 2 ^ (prefixWord ++ tailWord_297306).sum := by decide
  have hdescent : baseEnd_297306 < baseStart_297306 := by decide
  rcases family_descends (prefixWord ++ tailWord_297306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297327 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 7]
def baseStart_297327 : Nat := 118140960795 + 297327 * 2 ^ 59
def prefixEnd_297327 : Nat := 4983230072969 + 3 ^ 40 * 297327 * 2
def baseEnd_297327 : Nat := 135708144497300835951221

theorem tailTrace_297327 : CollatzResearch.WordTrace tailWord_297327 prefixEnd_297327 135708144497300835951221 := by
  unfold tailWord_297327
  simp only [CollatzResearch.WordTrace]
  refine ⟨10844406593842533253954235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7229604395895022169302823 10844406593842533253954235)
  ·
    refine ⟨16266609890763799880931353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10844406593842533253954235 16266609890763799880931353)
    ·
      refine ⟨12199957418072849910698515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16266609890763799880931353 12199957418072849910698515)
      ·
        refine ⟨18299936127109274866047773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12199957418072849910698515 18299936127109274866047773)
        ·
          refine ⟨6862476047665978074767915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18299936127109274866047773 6862476047665978074767915)
          ·
            refine ⟨10293714071498967112151873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6862476047665978074767915 10293714071498967112151873)
            ·
              refine ⟨7720285553624225334113905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10293714071498967112151873 7720285553624225334113905)
              ·
                refine ⟨5790214165218169000585429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7720285553624225334113905 5790214165218169000585429)
                ·
                  refine ⟨135708144497300835951221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5790214165218169000585429 135708144497300835951221)
                  ·
                    rfl

theorem cell20_297327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_297327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297327 prefixEnd_297327 := by exact prefixLift 297327
  have htrace : WordTrace (prefixWord ++ tailWord_297327) baseStart_297327 baseEnd_297327 := by
    simpa [prefixWord, tailWord_297327, baseEnd_297327] using wordTrace_append hprefix tailTrace_297327
  have hstable : (prefixWord ++ tailWord_297327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297327).length < 2 ^ (prefixWord ++ tailWord_297327).sum := by decide
  have hdescent : baseEnd_297327 < baseStart_297327 := by decide
  rcases family_descends (prefixWord ++ tailWord_297327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297354 : List Nat := [3, 1, 2, 5, 2, 7]
def baseStart_297354 : Nat := 118140960795 + 297354 * 2 ^ 59
def prefixEnd_297354 : Nat := 4983230072969 + 3 ^ 40 * 297354 * 2
def baseEnd_297354 : Nat := 5026684001222546001893

theorem tailTrace_297354 : CollatzResearch.WordTrace tailWord_297354 prefixEnd_297354 5026684001222546001893 := by
  unfold tailWord_297354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2711347841186179216296779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7230260909829811243458077 2711347841186179216296779)
  ·
    refine ⟨4067021761779268824445169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2711347841186179216296779 4067021761779268824445169)
    ·
      refine ⟨3050266321334451618333877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4067021761779268824445169 3050266321334451618333877)
      ·
        refine ⟨285962467625104839218801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3050266321334451618333877 285962467625104839218801)
        ·
          refine ⟨214471850718828629414101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285962467625104839218801 214471850718828629414101)
          ·
            refine ⟨5026684001222546001893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 214471850718828629414101 5026684001222546001893)
            ·
              rfl

theorem cell20_297354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 7].length) (baseStart_297354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297354 prefixEnd_297354 := by exact prefixLift 297354
  have htrace : WordTrace (prefixWord ++ tailWord_297354) baseStart_297354 baseEnd_297354 := by
    simpa [prefixWord, tailWord_297354, baseEnd_297354] using wordTrace_append hprefix tailTrace_297354
  have hstable : (prefixWord ++ tailWord_297354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297354).length < 2 ^ (prefixWord ++ tailWord_297354).sum := by decide
  have hdescent : baseEnd_297354 < baseStart_297354 := by decide
  rcases family_descends (prefixWord ++ tailWord_297354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297364 : List Nat := [2, 4, 2, 1, 3, 1, 1, 4, 2]
def baseStart_297364 : Nat := 118140960795 + 297364 * 2 ^ 59
def prefixEnd_297364 : Nat := 4983230072969 + 3 ^ 40 * 297364 * 2
def baseEnd_297364 : Nat := 135725032305493151717737

theorem tailTrace_297364 : CollatzResearch.WordTrace tailWord_297364 prefixEnd_297364 135725032305493151717737 := by
  unfold tailWord_297364
  simp only [CollatzResearch.WordTrace]
  refine ⟨5422878047354244286525573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7230504063138992382034097 5422878047354244286525573)
  ·
    refine ⟨1016789633878920803723545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5422878047354244286525573 1016789633878920803723545)
    ·
      refine ⟨762592225409190602792659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1016789633878920803723545 762592225409190602792659)
      ·
        refine ⟨1143888338113785904188989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 762592225409190602792659 1143888338113785904188989)
        ·
          refine ⟨428958126792669714070871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1143888338113785904188989 428958126792669714070871)
          ·
            refine ⟨643437190189004571106307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428958126792669714070871 643437190189004571106307)
            ·
              refine ⟨965155785283506856659461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643437190189004571106307 965155785283506856659461)
              ·
                refine ⟨180966709740657535623649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 965155785283506856659461 180966709740657535623649)
                ·
                  refine ⟨135725032305493151717737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180966709740657535623649 135725032305493151717737)
                  ·
                    rfl

theorem cell20_297364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_297364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297364 prefixEnd_297364 := by exact prefixLift 297364
  have htrace : WordTrace (prefixWord ++ tailWord_297364) baseStart_297364 baseEnd_297364 := by
    simpa [prefixWord, tailWord_297364, baseEnd_297364] using wordTrace_append hprefix tailTrace_297364
  have hstable : (prefixWord ++ tailWord_297364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297364).length < 2 ^ (prefixWord ++ tailWord_297364).sum := by decide
  have hdescent : baseEnd_297364 < baseStart_297364 := by decide
  rcases family_descends (prefixWord ++ tailWord_297364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297409 : List Nat := [1, 2, 7, 1, 1, 1, 7]
def baseStart_297409 : Nat := 118140960795 + 297409 * 2 ^ 59
def prefixEnd_297409 : Nat := 4983230072969 + 3 ^ 40 * 297409 * 2
def baseEnd_297409 : Nat := 15082841281296999468617

theorem tailTrace_297409 : CollatzResearch.WordTrace tailWord_297409 prefixEnd_297409 15082841281296999468617 := by
  unfold tailWord_297409
  simp only [CollatzResearch.WordTrace]
  refine ⟨10847397379545461258439281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7231598253030307505626187 10847397379545461258439281)
  ·
    refine ⟨8135548034659095943829461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10847397379545461258439281 8135548034659095943829461)
    ·
      refine ⟨190676907062322561183503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8135548034659095943829461 190676907062322561183503)
      ·
        refine ⟨286015360593483841775255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190676907062322561183503 286015360593483841775255)
        ·
          refine ⟨429023040890225762662883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286015360593483841775255 429023040890225762662883)
          ·
            refine ⟨643534561335338643994325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429023040890225762662883 643534561335338643994325)
            ·
              refine ⟨15082841281296999468617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 643534561335338643994325 15082841281296999468617)
              ·
                rfl

theorem cell20_297409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 7].length) (baseStart_297409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297409 prefixEnd_297409 := by exact prefixLift 297409
  have htrace : WordTrace (prefixWord ++ tailWord_297409) baseStart_297409 baseEnd_297409 := by
    simpa [prefixWord, tailWord_297409, baseEnd_297409] using wordTrace_append hprefix tailTrace_297409
  have hstable : (prefixWord ++ tailWord_297409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297409).length < 2 ^ (prefixWord ++ tailWord_297409).sum := by decide
  have hdescent : baseEnd_297409 < baseStart_297409 := by decide
  rcases family_descends (prefixWord ++ tailWord_297409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297434 : List Nat := [3, 1, 1, 2, 3, 1, 2, 7]
def baseStart_297434 : Nat := 118140960795 + 297434 * 2 ^ 59
def prefixEnd_297434 : Nat := 4983230072969 + 3 ^ 40 * 297434 * 2
def baseEnd_297434 : Nat := 45252327404294673128039

theorem tailTrace_297434 : CollatzResearch.WordTrace tailWord_297434 prefixEnd_297434 45252327404294673128039 := by
  unfold tailWord_297434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2712077301113722632024839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7232206136303260352066237 2712077301113722632024839)
  ·
    refine ⟨4068115951670583948037259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2712077301113722632024839 4068115951670583948037259)
    ·
      refine ⟨6102173927505875922055889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4068115951670583948037259 6102173927505875922055889)
      ·
        refine ⟨4576630445629406941541917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6102173927505875922055889 4576630445629406941541917)
        ·
          refine ⟨1716236417111027603078219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4576630445629406941541917 1716236417111027603078219)
          ·
            refine ⟨2574354625666541404617329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716236417111027603078219 2574354625666541404617329)
            ·
              refine ⟨1930765969249906053462997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2574354625666541404617329 1930765969249906053462997)
              ·
                refine ⟨45252327404294673128039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1930765969249906053462997 45252327404294673128039)
                ·
                  rfl

theorem cell20_297434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_297434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297434 prefixEnd_297434 := by exact prefixLift 297434
  have htrace : WordTrace (prefixWord ++ tailWord_297434) baseStart_297434 baseEnd_297434 := by
    simpa [prefixWord, tailWord_297434, baseEnd_297434] using wordTrace_append hprefix tailTrace_297434
  have hstable : (prefixWord ++ tailWord_297434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297434).length < 2 ^ (prefixWord ++ tailWord_297434).sum := by decide
  have hdescent : baseEnd_297434 < baseStart_297434 := by decide
  rcases family_descends (prefixWord ++ tailWord_297434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297485 : List Nat := [1, 7, 1, 1, 1, 2, 2, 5]
def baseStart_297485 : Nat := 118140960795 + 297485 * 2 ^ 59
def prefixEnd_297485 : Nat := 4983230072969 + 3 ^ 40 * 297485 * 2
def baseEnd_297485 : Nat := 45260086667518169561303

theorem tailTrace_297485 : CollatzResearch.WordTrace tailWord_297485 prefixEnd_297485 45260086667518169561303 := by
  unfold tailWord_297485
  simp only [CollatzResearch.WordTrace]
  refine ⟨10850169327270126238205909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7233446218180084158803939 10850169327270126238205909)
  ·
    refine ⟨254300843607893583707951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 10850169327270126238205909 254300843607893583707951)
    ·
      refine ⟨381451265411840375561927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254300843607893583707951 381451265411840375561927)
      ·
        refine ⟨572176898117760563342891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381451265411840375561927 572176898117760563342891)
        ·
          refine ⟨858265347176640845014337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572176898117760563342891 858265347176640845014337)
          ·
            refine ⟨643699010382480633760753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 858265347176640845014337 643699010382480633760753)
            ·
              refine ⟨482774257786860475320565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643699010382480633760753 482774257786860475320565)
              ·
                refine ⟨45260086667518169561303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 482774257786860475320565 45260086667518169561303)
                ·
                  rfl

theorem cell20_297485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 5].length) (baseStart_297485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297485 prefixEnd_297485 := by exact prefixLift 297485
  have htrace : WordTrace (prefixWord ++ tailWord_297485) baseStart_297485 baseEnd_297485 := by
    simpa [prefixWord, tailWord_297485, baseEnd_297485] using wordTrace_append hprefix tailTrace_297485
  have hstable : (prefixWord ++ tailWord_297485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297485).length < 2 ^ (prefixWord ++ tailWord_297485).sum := by decide
  have hdescent : baseEnd_297485 < baseStart_297485 := by decide
  rcases family_descends (prefixWord ++ tailWord_297485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297492 : List Nat := [2, 4, 3, 1, 1, 2, 1, 3, 3]
def baseStart_297492 : Nat := 118140960795 + 297492 * 2 ^ 59
def prefixEnd_297492 : Nat := 4983230072969 + 3 ^ 40 * 297492 * 2
def baseEnd_297492 : Nat := 135783454993293595450547

theorem tailTrace_297492 : CollatzResearch.WordTrace tailWord_297492 prefixEnd_297492 135783454993293595450547 := by
  unfold tailWord_297492
  simp only [CollatzResearch.WordTrace]
  refine ⟨5425212319122383216855365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7233616425496510955807153 5425212319122383216855365)
  ·
    refine ⟨1017227309835446853160381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5425212319122383216855365 1017227309835446853160381)
    ·
      refine ⟨381460241188292569935143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1017227309835446853160381 381460241188292569935143)
      ·
        refine ⟨572190361782438854902715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381460241188292569935143 572190361782438854902715)
        ·
          refine ⟨858285542673658282354073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572190361782438854902715 858285542673658282354073)
          ·
            refine ⟨643714157005243711765555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 858285542673658282354073 643714157005243711765555)
            ·
              refine ⟨965571235507865567648333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643714157005243711765555 965571235507865567648333)
              ·
                refine ⟨362089213315449587868125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 965571235507865567648333 362089213315449587868125)
                ·
                  refine ⟨135783454993293595450547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362089213315449587868125 135783454993293595450547)
                  ·
                    rfl

theorem cell20_297492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_297492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297492 prefixEnd_297492 := by exact prefixLift 297492
  have htrace : WordTrace (prefixWord ++ tailWord_297492) baseStart_297492 baseEnd_297492 := by
    simpa [prefixWord, tailWord_297492, baseEnd_297492] using wordTrace_append hprefix tailTrace_297492
  have hstable : (prefixWord ++ tailWord_297492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297492).length < 2 ^ (prefixWord ++ tailWord_297492).sum := by decide
  have hdescent : baseEnd_297492 < baseStart_297492 := by decide
  rcases family_descends (prefixWord ++ tailWord_297492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297537 : List Nat := [1, 2, 5, 1, 1, 3, 1, 4, 2]
def baseStart_297537 : Nat := 118140960795 + 297537 * 2 ^ 59
def prefixEnd_297537 : Nat := 4983230072969 + 3 ^ 40 * 297537 * 2
def baseEnd_297537 : Nat := 135803994219473438950363

theorem tailTrace_297537 : CollatzResearch.WordTrace tailWord_297537 prefixEnd_297537 135803994219473438950363 := by
  unfold tailWord_297537
  simp only [CollatzResearch.WordTrace]
  refine ⟨10852065923081739119098865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7234710615387826079399243 10852065923081739119098865)
  ·
    refine ⟨8139049442311304339324149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10852065923081739119098865 8139049442311304339324149)
    ·
      refine ⟨763035885216684781811639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8139049442311304339324149 763035885216684781811639)
      ·
        refine ⟨1144553827825027172717459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 763035885216684781811639 1144553827825027172717459)
        ·
          refine ⟨1716830741737540759076189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144553827825027172717459 1716830741737540759076189)
          ·
            refine ⟨643811528151577784653571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1716830741737540759076189 643811528151577784653571)
            ·
              refine ⟨965717292227366676980357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643811528151577784653571 965717292227366676980357)
              ·
                refine ⟨181071992292631251933817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 965717292227366676980357 181071992292631251933817)
                ·
                  refine ⟨135803994219473438950363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181071992292631251933817 135803994219473438950363)
                  ·
                    rfl

theorem cell20_297537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 2].length) (baseStart_297537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297537 prefixEnd_297537 := by exact prefixLift 297537
  have htrace : WordTrace (prefixWord ++ tailWord_297537) baseStart_297537 baseEnd_297537 := by
    simpa [prefixWord, tailWord_297537, baseEnd_297537] using wordTrace_append hprefix tailTrace_297537
  have hstable : (prefixWord ++ tailWord_297537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297537).length < 2 ^ (prefixWord ++ tailWord_297537).sum := by decide
  have hdescent : baseEnd_297537 < baseStart_297537 := by decide
  rcases family_descends (prefixWord ++ tailWord_297537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297540 : List Nat := [2, 3, 5, 1, 1, 2, 1, 5]
def baseStart_297540 : Nat := 118140960795 + 297540 * 2 ^ 59
def prefixEnd_297540 : Nat := 4983230072969 + 3 ^ 40 * 297540 * 2
def baseEnd_297540 : Nat := 45268454500406253950117

theorem tailTrace_297540 : CollatzResearch.WordTrace tailWord_297540 prefixEnd_297540 45268454500406253950117 := by
  unfold tailWord_297540
  simp only [CollatzResearch.WordTrace]
  refine ⟨5426087671035435315729037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7234783561380580420972049 5426087671035435315729037)
  ·
    refine ⟨2034782876638288243398389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5426087671035435315729037 2034782876638288243398389)
    ·
      refine ⟨190760894684839522818599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2034782876638288243398389 190760894684839522818599)
      ·
        refine ⟨286141342027259284227899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190760894684839522818599 286141342027259284227899)
        ·
          refine ⟨429212013040888926341849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286141342027259284227899 429212013040888926341849)
          ·
            refine ⟨321909009780666694756387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429212013040888926341849 321909009780666694756387)
            ·
              refine ⟨482863514671000042134581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321909009780666694756387 482863514671000042134581)
              ·
                refine ⟨45268454500406253950117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 482863514671000042134581 45268454500406253950117)
                ·
                  rfl

theorem cell20_297540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_297540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297540 prefixEnd_297540 := by exact prefixLift 297540
  have htrace : WordTrace (prefixWord ++ tailWord_297540) baseStart_297540 baseEnd_297540 := by
    simpa [prefixWord, tailWord_297540, baseEnd_297540] using wordTrace_append hprefix tailTrace_297540
  have hstable : (prefixWord ++ tailWord_297540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297540).length < 2 ^ (prefixWord ++ tailWord_297540).sum := by decide
  have hdescent : baseEnd_297540 < baseStart_297540 := by decide
  rcases family_descends (prefixWord ++ tailWord_297540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297589 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 5]
def baseStart_297589 : Nat := 118140960795 + 297589 * 2 ^ 59
def prefixEnd_297589 : Nat := 4983230072969 + 3 ^ 40 * 297589 * 2
def baseEnd_297589 : Nat := 135827728436392369216817

theorem tailTrace_297589 : CollatzResearch.WordTrace tailWord_297589 prefixEnd_297589 135827728436392369216817 := by
  unfold tailWord_297589
  simp only [CollatzResearch.WordTrace]
  refine ⟨10853962518893351999991821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7235975012595567999994547 10853962518893351999991821)
  ·
    refine ⟨4070235944585006999996933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10853962518893351999991821 4070235944585006999996933)
    ·
      refine ⟨763169239609688812499425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4070235944585006999996933 763169239609688812499425)
      ·
        refine ⟨572376929707266609374569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 763169239609688812499425 572376929707266609374569)
        ·
          refine ⟨429282697280449957030927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 572376929707266609374569 429282697280449957030927)
          ·
            refine ⟨643924045920674935546391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429282697280449957030927 643924045920674935546391)
            ·
              refine ⟨965886068881012403319587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 643924045920674935546391 965886068881012403319587)
              ·
                refine ⟨1448829103321518604979381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 965886068881012403319587 1448829103321518604979381)
                ·
                  refine ⟨135827728436392369216817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1448829103321518604979381 135827728436392369216817)
                  ·
                    rfl

theorem cell20_297589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_297589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297589 prefixEnd_297589 := by exact prefixLift 297589
  have htrace : WordTrace (prefixWord ++ tailWord_297589) baseStart_297589 baseEnd_297589 := by
    simpa [prefixWord, tailWord_297589, baseEnd_297589] using wordTrace_append hprefix tailTrace_297589
  have hstable : (prefixWord ++ tailWord_297589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297589).length < 2 ^ (prefixWord ++ tailWord_297589).sum := by decide
  have hdescent : baseEnd_297589 < baseStart_297589 := by decide
  rcases family_descends (prefixWord ++ tailWord_297589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297596 : List Nat := [2, 2, 2, 1, 1, 2, 4, 4, 2]
def baseStart_297596 : Nat := 118140960795 + 297596 * 2 ^ 59
def prefixEnd_297596 : Nat := 4983230072969 + 3 ^ 40 * 297596 * 2
def baseEnd_297596 : Nat := 135830923427131455983455

theorem tailTrace_297596 : CollatzResearch.WordTrace tailWord_297596 prefixEnd_297596 135830923427131455983455 := by
  unfold tailWord_297596
  simp only [CollatzResearch.WordTrace]
  refine ⟨5427108914933996097748321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7236145219911994796997761 5427108914933996097748321)
  ·
    refine ⟨4070331686200497073311241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5427108914933996097748321 4070331686200497073311241)
    ·
      refine ⟨3052748764650372804983431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4070331686200497073311241 3052748764650372804983431)
      ·
        refine ⟨4579123146975559207475147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3052748764650372804983431 4579123146975559207475147)
        ·
          refine ⟨6868684720463338811212721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4579123146975559207475147 6868684720463338811212721)
          ·
            refine ⟨5151513540347504108409541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6868684720463338811212721 5151513540347504108409541)
            ·
              refine ⟨965908788815157020326789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5151513540347504108409541 965908788815157020326789)
              ·
                refine ⟨181107897902841941311273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 965908788815157020326789 181107897902841941311273)
                ·
                  refine ⟨135830923427131455983455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181107897902841941311273 135830923427131455983455)
                  ·
                    rfl

theorem cell20_297596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_297596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297596 prefixEnd_297596 := by exact prefixLift 297596
  have htrace : WordTrace (prefixWord ++ tailWord_297596) baseStart_297596 baseEnd_297596 := by
    simpa [prefixWord, tailWord_297596, baseEnd_297596] using wordTrace_append hprefix tailTrace_297596
  have hstable : (prefixWord ++ tailWord_297596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297596).length < 2 ^ (prefixWord ++ tailWord_297596).sum := by decide
  have hdescent : baseEnd_297596 < baseStart_297596 := by decide
  rcases family_descends (prefixWord ++ tailWord_297596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297620 : List Nat := [2, 4, 2, 2, 1, 1, 4, 4]
def baseStart_297620 : Nat := 118140960795 + 297620 * 2 ^ 59
def prefixEnd_297620 : Nat := 4983230072969 + 3 ^ 40 * 297620 * 2
def baseEnd_297620 : Nat := 45280625893698013061119

theorem tailTrace_297620 : CollatzResearch.WordTrace tailWord_297620 prefixEnd_297620 45280625893698013061119 := by
  unfold tailWord_297620
  simp only [CollatzResearch.WordTrace]
  refine ⟨5427546590890522147185157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7236728787854029529580209 5427546590890522147185157)
  ·
    refine ⟨1017664985791972902597217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5427546590890522147185157 1017664985791972902597217)
    ·
      refine ⟨763248739343979676947913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1017664985791972902597217 763248739343979676947913)
      ·
        refine ⟨572436554507984757710935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 763248739343979676947913 572436554507984757710935)
        ·
          refine ⟨858654831761977136566403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572436554507984757710935 858654831761977136566403)
          ·
            refine ⟨1287982247642965704849605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858654831761977136566403 1287982247642965704849605)
            ·
              refine ⟨241496671433056069659301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1287982247642965704849605 241496671433056069659301)
              ·
                refine ⟨45280625893698013061119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241496671433056069659301 45280625893698013061119)
                ·
                  rfl

theorem cell20_297620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_297620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297620 prefixEnd_297620 := by exact prefixLift 297620
  have htrace : WordTrace (prefixWord ++ tailWord_297620) baseStart_297620 baseEnd_297620 := by
    simpa [prefixWord, tailWord_297620, baseEnd_297620] using wordTrace_append hprefix tailTrace_297620
  have hstable : (prefixWord ++ tailWord_297620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297620).length < 2 ^ (prefixWord ++ tailWord_297620).sum := by decide
  have hdescent : baseEnd_297620 < baseStart_297620 := by decide
  rcases family_descends (prefixWord ++ tailWord_297620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297624 : List Nat := [2, 1, 2, 4, 1, 1, 3, 6]
def baseStart_297624 : Nat := 118140960795 + 297624 * 2 ^ 59
def prefixEnd_297624 : Nat := 4983230072969 + 3 ^ 40 * 297624 * 2
def baseEnd_297624 : Nat := 45281234463362601016669

theorem tailTrace_297624 : CollatzResearch.WordTrace tailWord_297624 prefixEnd_297624 45281234463362601016669 := by
  unfold tailWord_297624
  simp only [CollatzResearch.WordTrace]
  refine ⟨5427619536883276488757963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7236826049177701985010617 5427619536883276488757963)
  ·
    refine ⟨8141429305324914733136945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5427619536883276488757963 8141429305324914733136945)
    ·
      refine ⟨6106071978993686049852709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8141429305324914733136945 6106071978993686049852709)
      ·
        refine ⟨1144888496061316134347383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6106071978993686049852709 1144888496061316134347383)
        ·
          refine ⟨1717332744091974201521075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144888496061316134347383 1717332744091974201521075)
          ·
            refine ⟨2575999116137961302281613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717332744091974201521075 2575999116137961302281613)
            ·
              refine ⟨965999668551735488355605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2575999116137961302281613 965999668551735488355605)
              ·
                refine ⟨45281234463362601016669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 965999668551735488355605 45281234463362601016669)
                ·
                  rfl

theorem cell20_297624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_297624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297624 prefixEnd_297624 := by exact prefixLift 297624
  have htrace : WordTrace (prefixWord ++ tailWord_297624) baseStart_297624 baseEnd_297624 := by
    simpa [prefixWord, tailWord_297624, baseEnd_297624] using wordTrace_append hprefix tailTrace_297624
  have hstable : (prefixWord ++ tailWord_297624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297624).length < 2 ^ (prefixWord ++ tailWord_297624).sum := by decide
  have hdescent : baseEnd_297624 < baseStart_297624 := by decide
  rcases family_descends (prefixWord ++ tailWord_297624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297651 : List Nat := [1, 1, 1, 2, 3, 5, 3, 2, 2]
def baseStart_297651 : Nat := 118140960795 + 297651 * 2 ^ 59
def prefixEnd_297651 : Nat := 4983230072969 + 3 ^ 40 * 297651 * 2
def baseEnd_297651 : Nat := 135856026925795709149897

theorem tailTrace_297651 : CollatzResearch.WordTrace tailWord_297651 prefixEnd_297651 135856026925795709149897 := by
  unfold tailWord_297651
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856223844668736588748807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7237482563112491059165871 10856223844668736588748807)
  ·
    refine ⟨16284335767003104883123211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10856223844668736588748807 16284335767003104883123211)
    ·
      refine ⟨24426503650504657324684817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16284335767003104883123211 24426503650504657324684817)
      ·
        refine ⟨18319877737878492993513613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24426503650504657324684817 18319877737878492993513613)
        ·
          refine ⟨6869954151704434872567605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18319877737878492993513613 6869954151704434872567605)
          ·
            refine ⟨644058201722290769303213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6869954151704434872567605 644058201722290769303213)
            ·
              refine ⟨241521825645859038488705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 644058201722290769303213 241521825645859038488705)
              ·
                refine ⟨181141369234394278866529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241521825645859038488705 181141369234394278866529)
                ·
                  refine ⟨135856026925795709149897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181141369234394278866529 135856026925795709149897)
                  ·
                    rfl

theorem cell20_297651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 2].length) (baseStart_297651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297651 prefixEnd_297651 := by exact prefixLift 297651
  have htrace : WordTrace (prefixWord ++ tailWord_297651) baseStart_297651 baseEnd_297651 := by
    simpa [prefixWord, tailWord_297651, baseEnd_297651] using wordTrace_append hprefix tailTrace_297651
  have hstable : (prefixWord ++ tailWord_297651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297651).length < 2 ^ (prefixWord ++ tailWord_297651).sum := by decide
  have hdescent : baseEnd_297651 < baseStart_297651 := by decide
  rcases family_descends (prefixWord ++ tailWord_297651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297724 : List Nat := [2, 2, 2, 1, 3, 2, 2, 3, 3]
def baseStart_297724 : Nat := 118140960795 + 297724 * 2 ^ 59
def prefixEnd_297724 : Nat := 4983230072969 + 3 ^ 40 * 297724 * 2
def baseEnd_297724 : Nat := 135889346114931899716265

theorem tailTrace_297724 : CollatzResearch.WordTrace tailWord_297724 prefixEnd_297724 135889346114931899716265 := by
  unfold tailWord_297724
  simp only [CollatzResearch.WordTrace]
  refine ⟨5429443186702135028078113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7239257582269513370770817 5429443186702135028078113)
  ·
    refine ⟨4072082390026601271058585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5429443186702135028078113 4072082390026601271058585)
    ·
      refine ⟨3054061792519950953293939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4072082390026601271058585 3054061792519950953293939)
      ·
        refine ⟨4581092688779926429940909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3054061792519950953293939 4581092688779926429940909)
        ·
          refine ⟨1717909758292472411227841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4581092688779926429940909 1717909758292472411227841)
          ·
            refine ⟨1288432318719354308420881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1717909758292472411227841 1288432318719354308420881)
            ·
              refine ⟨966324239039515731315661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1288432318719354308420881 966324239039515731315661)
              ·
                refine ⟨362371589639818399243373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 966324239039515731315661 362371589639818399243373)
                ·
                  refine ⟨135889346114931899716265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362371589639818399243373 135889346114931899716265)
                  ·
                    rfl

theorem cell20_297724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_297724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297724 prefixEnd_297724 := by exact prefixLift 297724
  have htrace : WordTrace (prefixWord ++ tailWord_297724) baseStart_297724 baseEnd_297724 := by
    simpa [prefixWord, tailWord_297724, baseEnd_297724] using wordTrace_append hprefix tailTrace_297724
  have hstable : (prefixWord ++ tailWord_297724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297724).length < 2 ^ (prefixWord ++ tailWord_297724).sum := by decide
  have hdescent : baseEnd_297724 < baseStart_297724 := by decide
  rcases family_descends (prefixWord ++ tailWord_297724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297752 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 8]
def baseStart_297752 : Nat := 118140960795 + 297752 * 2 ^ 59
def prefixEnd_297752 : Nat := 4983230072969 + 3 ^ 40 * 297752 * 2
def baseEnd_297752 : Nat := 135902126077888246782817

theorem tailTrace_297752 : CollatzResearch.WordTrace tailWord_297752 prefixEnd_297752 135902126077888246782817 := by
  unfold tailWord_297752
  simp only [CollatzResearch.WordTrace]
  refine ⟨5429953808651415419087755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7239938411535220558783673 5429953808651415419087755)
  ·
    refine ⟨8144930712977123128631633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5429953808651415419087755 8144930712977123128631633)
    ·
      refine ⟨6108698034732842346473725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8144930712977123128631633 6108698034732842346473725)
      ·
        refine ⟨2290761763024815879927647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6108698034732842346473725 2290761763024815879927647)
        ·
          refine ⟨3436142644537223819891471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290761763024815879927647 3436142644537223819891471)
          ·
            refine ⟨5154213966805835729837207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3436142644537223819891471 5154213966805835729837207)
            ·
              refine ⟨7731320950208753594755811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5154213966805835729837207 7731320950208753594755811)
              ·
                refine ⟨11596981425313130392133717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7731320950208753594755811 11596981425313130392133717)
                ·
                  refine ⟨135902126077888246782817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11596981425313130392133717 135902126077888246782817)
                  ·
                    rfl

theorem cell20_297752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_297752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297752 prefixEnd_297752 := by exact prefixLift 297752
  have htrace : WordTrace (prefixWord ++ tailWord_297752) baseStart_297752 baseEnd_297752 := by
    simpa [prefixWord, tailWord_297752, baseEnd_297752] using wordTrace_append hprefix tailTrace_297752
  have hstable : (prefixWord ++ tailWord_297752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297752).length < 2 ^ (prefixWord ++ tailWord_297752).sum := by decide
  have hdescent : baseEnd_297752 < baseStart_297752 := by decide
  rcases family_descends (prefixWord ++ tailWord_297752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297762 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_297762 : Nat := 118140960795 + 297762 * 2 ^ 59
def prefixEnd_297762 : Nat := 4983230072969 + 3 ^ 40 * 297762 * 2
def baseEnd_297762 : Nat := 135906690350372656449443

theorem tailTrace_297762 : CollatzResearch.WordTrace tailWord_297762 prefixEnd_297762 135906690350372656449443 := by
  unfold tailWord_297762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2715068086816650636509885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7240181564844401697359693 2715068086816650636509885)
  ·
    refine ⟨1018150532556243988691207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2715068086816650636509885 1018150532556243988691207)
    ·
      refine ⟨1527225798834365983036811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1018150532556243988691207 1527225798834365983036811)
      ·
        refine ⟨2290838698251548974555217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1527225798834365983036811 2290838698251548974555217)
        ·
          refine ⟨1718129023688661730916413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2290838698251548974555217 1718129023688661730916413)
          ·
            refine ⟨644298383883248149093655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1718129023688661730916413 644298383883248149093655)
            ·
              refine ⟨966447575824872223640483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644298383883248149093655 966447575824872223640483)
              ·
                refine ⟨1449671363737308335460725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966447575824872223640483 1449671363737308335460725)
                ·
                  refine ⟨135906690350372656449443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1449671363737308335460725 135906690350372656449443)
                  ·
                    rfl

theorem cell20_297762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_297762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297762 prefixEnd_297762 := by exact prefixLift 297762
  have htrace : WordTrace (prefixWord ++ tailWord_297762) baseStart_297762 baseEnd_297762 := by
    simpa [prefixWord, tailWord_297762, baseEnd_297762] using wordTrace_append hprefix tailTrace_297762
  have hstable : (prefixWord ++ tailWord_297762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297762).length < 2 ^ (prefixWord ++ tailWord_297762).sum := by decide
  have hdescent : baseEnd_297762 < baseStart_297762 := by decide
  rcases family_descends (prefixWord ++ tailWord_297762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297779 : List Nat := [1, 1, 1, 2, 6, 2, 3, 1, 3]
def baseStart_297779 : Nat := 118140960795 + 297779 * 2 ^ 59
def prefixEnd_297779 : Nat := 4983230072969 + 3 ^ 40 * 297779 * 2
def baseEnd_297779 : Nat := 135914449613596152882707

theorem tailTrace_297779 : CollatzResearch.WordTrace tailWord_297779 prefixEnd_297779 135914449613596152882707 := by
  unfold tailWord_297779
  simp only [CollatzResearch.WordTrace]
  refine ⟨10860892388205014449408391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7240594925470009632938927 10860892388205014449408391)
  ·
    refine ⟨16291338582307521674112587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10860892388205014449408391 16291338582307521674112587)
    ·
      refine ⟨24437007873461282511168881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16291338582307521674112587 24437007873461282511168881)
      ·
        refine ⟨18327755905095961883376661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24437007873461282511168881 18327755905095961883376661)
        ·
          refine ⟨859113558051373213283281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18327755905095961883376661 859113558051373213283281)
          ·
            refine ⟨644335168538529909962461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 859113558051373213283281 644335168538529909962461)
            ·
              refine ⟨241625688201948716235923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 644335168538529909962461 241625688201948716235923)
              ·
                refine ⟨362438532302923074353885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241625688201948716235923 362438532302923074353885)
                ·
                  refine ⟨135914449613596152882707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362438532302923074353885 135914449613596152882707)
                  ·
                    rfl

theorem cell20_297779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 3].length) (baseStart_297779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297779 prefixEnd_297779 := by exact prefixLift 297779
  have htrace : WordTrace (prefixWord ++ tailWord_297779) baseStart_297779 baseEnd_297779 := by
    simpa [prefixWord, tailWord_297779, baseEnd_297779] using wordTrace_append hprefix tailTrace_297779
  have hstable : (prefixWord ++ tailWord_297779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297779).length < 2 ^ (prefixWord ++ tailWord_297779).sum := by decide
  have hdescent : baseEnd_297779 < baseStart_297779 := by decide
  rcases family_descends (prefixWord ++ tailWord_297779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297789 : List Nat := [1, 4, 1, 4, 3, 1, 2, 4]
def baseStart_297789 : Nat := 118140960795 + 297789 * 2 ^ 59
def prefixEnd_297789 : Nat := 4983230072969 + 3 ^ 40 * 297789 * 2
def baseEnd_297789 : Nat := 45306337962026854183111

theorem tailTrace_297789 : CollatzResearch.WordTrace tailWord_297789 prefixEnd_297789 45306337962026854183111 := by
  unfold tailWord_297789
  simp only [CollatzResearch.WordTrace]
  refine ⟨10861257118168786157272421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7240838078779190771514947 10861257118168786157272421)
  ·
    refine ⟨2036485709656647404488579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10861257118168786157272421 2036485709656647404488579)
    ·
      refine ⟨3054728564484971106732869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2036485709656647404488579 3054728564484971106732869)
      ·
        refine ⟨572761605840932082512413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3054728564484971106732869 572761605840932082512413)
        ·
          refine ⟨214785602190349530942155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 572761605840932082512413 214785602190349530942155)
          ·
            refine ⟨322178403285524296413233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214785602190349530942155 322178403285524296413233)
            ·
              refine ⟨241633802464143222309925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322178403285524296413233 241633802464143222309925)
              ·
                refine ⟨45306337962026854183111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241633802464143222309925 45306337962026854183111)
                ·
                  rfl

theorem cell20_297789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 4].length) (baseStart_297789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297789 prefixEnd_297789 := by exact prefixLift 297789
  have htrace : WordTrace (prefixWord ++ tailWord_297789) baseStart_297789 baseEnd_297789 := by
    simpa [prefixWord, tailWord_297789, baseEnd_297789] using wordTrace_append hprefix tailTrace_297789
  have hstable : (prefixWord ++ tailWord_297789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297789).length < 2 ^ (prefixWord ++ tailWord_297789).sum := by decide
  have hdescent : baseEnd_297789 < baseStart_297789 := by decide
  rcases family_descends (prefixWord ++ tailWord_297789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297820 : List Nat := [2, 2, 4, 2, 1, 2, 3, 2, 2]
def baseStart_297820 : Nat := 118140960795 + 297820 * 2 ^ 59
def prefixEnd_297820 : Nat := 4983230072969 + 3 ^ 40 * 297820 * 2
def baseEnd_297820 : Nat := 135933163130782232515873

theorem tailTrace_297820 : CollatzResearch.WordTrace tailWord_297820 prefixEnd_297820 135933163130782232515873 := by
  unfold tailWord_297820
  simp only [CollatzResearch.WordTrace]
  refine ⟨5431193890528239225825457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7241591854037652301100609 5431193890528239225825457)
  ·
    refine ⟨4073395417896179419369093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5431193890528239225825457 4073395417896179419369093)
    ·
      refine ⟨763761640855533641131705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4073395417896179419369093 763761640855533641131705)
      ·
        refine ⟨572821230641650230848779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 763761640855533641131705 572821230641650230848779)
        ·
          refine ⟨859231845962475346273169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572821230641650230848779 859231845962475346273169)
          ·
            refine ⟨644423884471856509704877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 859231845962475346273169 644423884471856509704877)
            ·
              refine ⟨241658956676946191139329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 644423884471856509704877 241658956676946191139329)
              ·
                refine ⟨181244217507709643354497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 241658956676946191139329 181244217507709643354497)
                ·
                  refine ⟨135933163130782232515873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181244217507709643354497 135933163130782232515873)
                  ·
                    rfl

theorem cell20_297820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_297820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297820 prefixEnd_297820 := by exact prefixLift 297820
  have htrace : WordTrace (prefixWord ++ tailWord_297820) baseStart_297820 baseEnd_297820 := by
    simpa [prefixWord, tailWord_297820, baseEnd_297820] using wordTrace_append hprefix tailTrace_297820
  have hstable : (prefixWord ++ tailWord_297820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297820).length < 2 ^ (prefixWord ++ tailWord_297820).sum := by decide
  have hdescent : baseEnd_297820 < baseStart_297820 := by decide
  rcases family_descends (prefixWord ++ tailWord_297820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297835 : List Nat := [1, 1, 1, 1, 2, 2, 5, 7]
def baseStart_297835 : Nat := 118140960795 + 297835 * 2 ^ 59
def prefixEnd_297835 : Nat := 4983230072969 + 3 ^ 40 * 297835 * 2
def baseEnd_297835 : Nat := 45313336513169615671937

theorem tailTrace_297835 : CollatzResearch.WordTrace tailWord_297835 prefixEnd_297835 45313336513169615671937 := by
  unfold tailWord_297835
  simp only [CollatzResearch.WordTrace]
  refine ⟨10862934876002136013446959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7241956584001424008964639 10862934876002136013446959)
  ·
    refine ⟨16294402314003204020170439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10862934876002136013446959 16294402314003204020170439)
    ·
      refine ⟨24441603471004806030255659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16294402314003204020170439 24441603471004806030255659)
      ·
        refine ⟨36662405206507209045383489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24441603471004806030255659 36662405206507209045383489)
        ·
          refine ⟨27496803904880406784037617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36662405206507209045383489 27496803904880406784037617)
          ·
            refine ⟨20622602928660305088028213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27496803904880406784037617 20622602928660305088028213)
            ·
              refine ⟨1933369024561903602002645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20622602928660305088028213 1933369024561903602002645)
              ·
                refine ⟨45313336513169615671937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1933369024561903602002645 45313336513169615671937)
                ·
                  rfl

theorem cell20_297835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 7].length) (baseStart_297835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297835 prefixEnd_297835 := by exact prefixLift 297835
  have htrace : WordTrace (prefixWord ++ tailWord_297835) baseStart_297835 baseEnd_297835 := by
    simpa [prefixWord, tailWord_297835, baseEnd_297835] using wordTrace_append hprefix tailTrace_297835
  have hstable : (prefixWord ++ tailWord_297835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297835).length < 2 ^ (prefixWord ++ tailWord_297835).sum := by decide
  have hdescent : baseEnd_297835 < baseStart_297835 := by decide
  rcases family_descends (prefixWord ++ tailWord_297835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297897 : List Nat := [1, 2, 1, 1, 1, 1, 5, 5, 3]
def baseStart_297897 : Nat := 118140960795 + 297897 * 2 ^ 59
def prefixEnd_297897 : Nat := 4983230072969 + 3 ^ 40 * 297897 * 2
def baseEnd_297897 : Nat := 135968308028912186948891

theorem tailTrace_297897 : CollatzResearch.WordTrace tailWord_297897 prefixEnd_297897 135968308028912186948891 := by
  unfold tailWord_297897
  simp only [CollatzResearch.WordTrace]
  refine ⟨10865196201777520602203945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7243464134518347068135963 10865196201777520602203945)
  ·
    refine ⟨8148897151333140451652959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10865196201777520602203945 8148897151333140451652959)
    ·
      refine ⟨12223345726999710677479439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8148897151333140451652959 12223345726999710677479439)
      ·
        refine ⟨18335018590499566016219159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12223345726999710677479439 18335018590499566016219159)
        ·
          refine ⟨27502527885749349024328739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18335018590499566016219159 27502527885749349024328739)
          ·
            refine ⟨41253791828624023536493109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27502527885749349024328739 41253791828624023536493109)
            ·
              refine ⟨3867542983933502206546229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41253791828624023536493109 3867542983933502206546229)
              ·
                refine ⟨362582154743765831863709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3867542983933502206546229 362582154743765831863709)
                ·
                  refine ⟨135968308028912186948891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362582154743765831863709 135968308028912186948891)
                  ·
                    rfl

theorem cell20_297897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_297897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297897 prefixEnd_297897 := by exact prefixLift 297897
  have htrace : WordTrace (prefixWord ++ tailWord_297897) baseStart_297897 baseEnd_297897 := by
    simpa [prefixWord, tailWord_297897, baseEnd_297897] using wordTrace_append hprefix tailTrace_297897
  have hstable : (prefixWord ++ tailWord_297897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297897).length < 2 ^ (prefixWord ++ tailWord_297897).sum := by decide
  have hdescent : baseEnd_297897 < baseStart_297897 := by decide
  rcases family_descends (prefixWord ++ tailWord_297897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297911 : List Nat := [1, 1, 3, 1, 3, 1, 2, 8]
def baseStart_297911 : Nat := 118140960795 + 297911 * 2 ^ 59
def prefixEnd_297911 : Nat := 4983230072969 + 3 ^ 40 * 297911 * 2
def baseEnd_297911 : Nat := 45324899336796786827389

theorem tailTrace_297911 : CollatzResearch.WordTrace tailWord_297911 prefixEnd_297911 45324899336796786827389 := by
  unfold tailWord_297911
  simp only [CollatzResearch.WordTrace]
  refine ⟨10865706823726800993213587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7243804549151200662142391 10865706823726800993213587)
  ·
    refine ⟨16298560235590201489820381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10865706823726800993213587 16298560235590201489820381)
    ·
      refine ⟨6111960088346325558682643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16298560235590201489820381 6111960088346325558682643)
      ·
        refine ⟨9167940132519488338023965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6111960088346325558682643 9167940132519488338023965)
        ·
          refine ⟨3437977549694808126758987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9167940132519488338023965 3437977549694808126758987)
          ·
            refine ⟨5156966324542212190138481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3437977549694808126758987 5156966324542212190138481)
            ·
              refine ⟨3867724743406659142603861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5156966324542212190138481 3867724743406659142603861)
              ·
                refine ⟨45324899336796786827389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3867724743406659142603861 45324899336796786827389)
                ·
                  rfl

theorem cell20_297911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 8].length) (baseStart_297911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297911 prefixEnd_297911 := by exact prefixLift 297911
  have htrace : WordTrace (prefixWord ++ tailWord_297911) baseStart_297911 baseEnd_297911 := by
    simpa [prefixWord, tailWord_297911, baseEnd_297911] using wordTrace_append hprefix tailTrace_297911
  have hstable : (prefixWord ++ tailWord_297911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297911).length < 2 ^ (prefixWord ++ tailWord_297911).sum := by decide
  have hdescent : baseEnd_297911 < baseStart_297911 := by decide
  rcases family_descends (prefixWord ++ tailWord_297911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297917 : List Nat := [1, 4, 1, 2, 4, 1, 2, 3, 2]
def baseStart_297917 : Nat := 118140960795 + 297917 * 2 ^ 59
def prefixEnd_297917 : Nat := 4983230072969 + 3 ^ 40 * 297917 * 2
def baseEnd_297917 : Nat := 135977436573881006282143

theorem tailTrace_297917 : CollatzResearch.WordTrace tailWord_297917 prefixEnd_297917 135977436573881006282143 := by
  unfold tailWord_297917
  simp only [CollatzResearch.WordTrace]
  refine ⟨10865925661705064017932005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7243950441136709345288003 10865925661705064017932005)
  ·
    refine ⟨2037361061569699503362251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10865925661705064017932005 2037361061569699503362251)
    ·
      refine ⟨3056041592354549255043377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2037361061569699503362251 3056041592354549255043377)
      ·
        refine ⟨2292031194265911941282533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3056041592354549255043377 2292031194265911941282533)
        ·
          refine ⟨429755848924858488990475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2292031194265911941282533 429755848924858488990475)
          ·
            refine ⟨644633773387287733485713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429755848924858488990475 644633773387287733485713)
            ·
              refine ⟨483475330040465800114285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 644633773387287733485713 483475330040465800114285)
              ·
                refine ⟨181303248765174675042857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 483475330040465800114285 181303248765174675042857)
                ·
                  refine ⟨135977436573881006282143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181303248765174675042857 135977436573881006282143)
                  ·
                    rfl

theorem cell20_297917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_297917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297917 prefixEnd_297917 := by exact prefixLift 297917
  have htrace : WordTrace (prefixWord ++ tailWord_297917) baseStart_297917 baseEnd_297917 := by
    simpa [prefixWord, tailWord_297917, baseEnd_297917] using wordTrace_append hprefix tailTrace_297917
  have hstable : (prefixWord ++ tailWord_297917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297917).length < 2 ^ (prefixWord ++ tailWord_297917).sum := by decide
  have hdescent : baseEnd_297917 < baseStart_297917 := by decide
  rcases family_descends (prefixWord ++ tailWord_297917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297928 : List Nat := [2, 1, 3, 1, 5, 1, 7]
def baseStart_297928 : Nat := 118140960795 + 297928 * 2 ^ 59
def prefixEnd_297928 : Nat := 4983230072969 + 3 ^ 40 * 297928 * 2
def baseEnd_297928 : Nat := 15109161919290428546159

theorem tailTrace_297928 : CollatzResearch.WordTrace tailWord_297928 prefixEnd_297928 15109161919290428546159 := by
  unfold tailWord_297928
  simp only [CollatzResearch.WordTrace]
  refine ⟨5433163432332606448291219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7244217909776808597721625 5433163432332606448291219)
  ·
    refine ⟨8149745148498909672436829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5433163432332606448291219 8149745148498909672436829)
    ·
      refine ⟨3056154430687091127163811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8149745148498909672436829 3056154430687091127163811)
      ·
        refine ⟨4584231646030636690745717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3056154430687091127163811 4584231646030636690745717)
        ·
          refine ⟨429771716815372189757411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4584231646030636690745717 429771716815372189757411)
          ·
            refine ⟨644657575223058284636117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429771716815372189757411 644657575223058284636117)
            ·
              refine ⟨15109161919290428546159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 644657575223058284636117 15109161919290428546159)
              ·
                rfl

theorem cell20_297928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 7].length) (baseStart_297928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297928 prefixEnd_297928 := by exact prefixLift 297928
  have htrace : WordTrace (prefixWord ++ tailWord_297928) baseStart_297928 baseEnd_297928 := by
    simpa [prefixWord, tailWord_297928, baseEnd_297928] using wordTrace_append hprefix tailTrace_297928
  have hstable : (prefixWord ++ tailWord_297928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297928).length < 2 ^ (prefixWord ++ tailWord_297928).sum := by decide
  have hdescent : baseEnd_297928 < baseStart_297928 := by decide
  rcases family_descends (prefixWord ++ tailWord_297928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297935 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 5]
def baseStart_297935 : Nat := 118140960795 + 297935 * 2 ^ 59
def prefixEnd_297935 : Nat := 4983230072969 + 3 ^ 40 * 297935 * 2
def baseEnd_297935 : Nat := 135985652264352943682069

theorem tailTrace_297935 : CollatzResearch.WordTrace tailWord_297935 prefixEnd_297935 135985652264352943682069 := by
  unfold tailWord_297935
  simp only [CollatzResearch.WordTrace]
  refine ⟨10866582175639853092087259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7244388117093235394724839 10866582175639853092087259)
  ·
    refine ⟨16299873263459779638130889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10866582175639853092087259 16299873263459779638130889)
    ·
      refine ⟨12224904947594834728598167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16299873263459779638130889 12224904947594834728598167)
      ·
        refine ⟨18337357421392252092897251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12224904947594834728598167 18337357421392252092897251)
        ·
          refine ⟨27506036132088378139345877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18337357421392252092897251 27506036132088378139345877)
          ·
            refine ⟨644672721845821362640919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 27506036132088378139345877 644672721845821362640919)
            ·
              refine ⟨967009082768732043961379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644672721845821362640919 967009082768732043961379)
              ·
                refine ⟨1450513624153098065942069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 967009082768732043961379 1450513624153098065942069)
                ·
                  refine ⟨135985652264352943682069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1450513624153098065942069 135985652264352943682069)
                  ·
                    rfl

theorem cell20_297935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_297935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297935 prefixEnd_297935 := by exact prefixLift 297935
  have htrace : WordTrace (prefixWord ++ tailWord_297935) baseStart_297935 baseEnd_297935 := by
    simpa [prefixWord, tailWord_297935, baseEnd_297935] using wordTrace_append hprefix tailTrace_297935
  have hstable : (prefixWord ++ tailWord_297935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297935).length < 2 ^ (prefixWord ++ tailWord_297935).sum := by decide
  have hdescent : baseEnd_297935 < baseStart_297935 := by decide
  rcases family_descends (prefixWord ++ tailWord_297935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297938 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_297938 : Nat := 118140960795 + 297938 * 2 ^ 59
def prefixEnd_297938 : Nat := 4983230072969 + 3 ^ 40 * 297938 * 2
def baseEnd_297938 : Nat := 135987021546098266582057

theorem tailTrace_297938 : CollatzResearch.WordTrace tailWord_297938 prefixEnd_297938 135987021546098266582057 := by
  unfold tailWord_297938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2716672898657246151111617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7244461063085989736297645 2716672898657246151111617)
  ·
    refine ⟨2037504673992934613333713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2716672898657246151111617 2037504673992934613333713)
    ·
      refine ⟨1528128505494700960000285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2037504673992934613333713 1528128505494700960000285)
      ·
        refine ⟨573048189560512860000107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1528128505494700960000285 573048189560512860000107)
        ·
          refine ⟨859572284340769290000161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573048189560512860000107 859572284340769290000161)
          ·
            refine ⟨644679213255576967500121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 859572284340769290000161 644679213255576967500121)
            ·
              refine ⟨483509409941682725625091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 644679213255576967500121 483509409941682725625091)
              ·
                refine ⟨725264114912524088437637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483509409941682725625091 725264114912524088437637)
                ·
                  refine ⟨135987021546098266582057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 725264114912524088437637 135987021546098266582057)
                  ·
                    rfl

theorem cell20_297938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_297938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297938 prefixEnd_297938 := by exact prefixLift 297938
  have htrace : WordTrace (prefixWord ++ tailWord_297938) baseStart_297938 baseEnd_297938 := by
    simpa [prefixWord, tailWord_297938, baseEnd_297938] using wordTrace_append hprefix tailTrace_297938
  have hstable : (prefixWord ++ tailWord_297938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297938).length < 2 ^ (prefixWord ++ tailWord_297938).sum := by decide
  have hdescent : baseEnd_297938 < baseStart_297938 := by decide
  rcases family_descends (prefixWord ++ tailWord_297938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297959 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 4]
def baseStart_297959 : Nat := 118140960795 + 297959 * 2 ^ 59
def prefixEnd_297959 : Nat := 4983230072969 + 3 ^ 40 * 297959 * 2
def baseEnd_297959 : Nat := 135996606518315526881971

theorem tailTrace_297959 : CollatzResearch.WordTrace tailWord_297959 prefixEnd_297959 135996606518315526881971 := by
  unfold tailWord_297959
  simp only [CollatzResearch.WordTrace]
  refine ⟨10867457527552905190960931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7244971685035270127307287 10867457527552905190960931)
  ·
    refine ⟨16301186291329357786441397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10867457527552905190960931 16301186291329357786441397)
    ·
      refine ⟨1528236214812127292478881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16301186291329357786441397 1528236214812127292478881)
      ·
        refine ⟨1146177161109095469359161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1528236214812127292478881 1146177161109095469359161)
        ·
          refine ⟨859632870831821602019371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1146177161109095469359161 859632870831821602019371)
          ·
            refine ⟨1289449306247732403029057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859632870831821602019371 1289449306247732403029057)
            ·
              refine ⟨967086979685799302271793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1289449306247732403029057 967086979685799302271793)
              ·
                refine ⟨725315234764349476703845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967086979685799302271793 725315234764349476703845)
                ·
                  refine ⟨135996606518315526881971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 725315234764349476703845 135996606518315526881971)
                  ·
                    rfl

theorem cell20_297959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_297959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_297959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_297959 prefixEnd_297959 := by exact prefixLift 297959
  have htrace : WordTrace (prefixWord ++ tailWord_297959) baseStart_297959 baseEnd_297959 := by
    simpa [prefixWord, tailWord_297959, baseEnd_297959] using wordTrace_append hprefix tailTrace_297959
  have hstable : (prefixWord ++ tailWord_297959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297959).length < 2 ^ (prefixWord ++ tailWord_297959).sum := by decide
  have hdescent : baseEnd_297959 < baseStart_297959 := by decide
  rcases family_descends (prefixWord ++ tailWord_297959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298007 : List Nat := [1, 1, 3, 5, 1, 1, 4, 1, 3]
def baseStart_298007 : Nat := 118140960795 + 298007 * 2 ^ 59
def prefixEnd_298007 : Nat := 4983230072969 + 3 ^ 40 * 298007 * 2
def baseEnd_298007 : Nat := 136018515026240693281775

theorem tailTrace_298007 : CollatzResearch.WordTrace tailWord_298007 prefixEnd_298007 136018515026240693281775 := by
  unfold tailWord_298007
  simp only [CollatzResearch.WordTrace]
  refine ⟨10869208231379009388708275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7246138820919339592472183 10869208231379009388708275)
  ·
    refine ⟨16303812347068514083062413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10869208231379009388708275 16303812347068514083062413)
    ·
      refine ⟨6113929630150692781148405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16303812347068514083062413 6113929630150692781148405)
      ·
        refine ⟨573180902826627448232663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6113929630150692781148405 573180902826627448232663)
        ·
          refine ⟨859771354239941172348995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573180902826627448232663 859771354239941172348995)
          ·
            refine ⟨1289657031359911758523493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859771354239941172348995 1289657031359911758523493)
            ·
              refine ⟨241810693379983454723155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1289657031359911758523493 241810693379983454723155)
              ·
                refine ⟨362716040069975182084733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241810693379983454723155 362716040069975182084733)
                ·
                  refine ⟨136018515026240693281775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362716040069975182084733 136018515026240693281775)
                  ·
                    rfl

theorem cell20_298007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 1, 3].length) (baseStart_298007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298007 prefixEnd_298007 := by exact prefixLift 298007
  have htrace : WordTrace (prefixWord ++ tailWord_298007) baseStart_298007 baseEnd_298007 := by
    simpa [prefixWord, tailWord_298007, baseEnd_298007] using wordTrace_append hprefix tailTrace_298007
  have hstable : (prefixWord ++ tailWord_298007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298007).length < 2 ^ (prefixWord ++ tailWord_298007).sum := by decide
  have hdescent : baseEnd_298007 < baseStart_298007 := by decide
  rcases family_descends (prefixWord ++ tailWord_298007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298035 : List Nat := [1, 1, 1, 2, 4, 1, 1, 7, 2]
def baseStart_298035 : Nat := 118140960795 + 298035 * 2 ^ 59
def prefixEnd_298035 : Nat := 4983230072969 + 3 ^ 40 * 298035 * 2
def baseEnd_298035 : Nat := 136031294989197040348327

theorem tailTrace_298035 : CollatzResearch.WordTrace tailWord_298035 prefixEnd_298035 136031294989197040348327 := by
  unfold tailWord_298035
  simp only [CollatzResearch.WordTrace]
  refine ⟨10870229475277570170727559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7246819650185046780485039 10870229475277570170727559)
  ·
    refine ⟨16305344212916355256091339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10870229475277570170727559 16305344212916355256091339)
    ·
      refine ⟨24458016319374532884137009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16305344212916355256091339 24458016319374532884137009)
      ·
        refine ⟨18343512239530899663102757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24458016319374532884137009 18343512239530899663102757)
        ·
          refine ⟨3439408544912043686831767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18343512239530899663102757 3439408544912043686831767)
          ·
            refine ⟨5159112817368065530247651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3439408544912043686831767 5159112817368065530247651)
            ·
              refine ⟨7738669226052098295371477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5159112817368065530247651 7738669226052098295371477)
              ·
                refine ⟨181375059985596053797769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7738669226052098295371477 181375059985596053797769)
                ·
                  refine ⟨136031294989197040348327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181375059985596053797769 136031294989197040348327)
                  ·
                    rfl

theorem cell20_298035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 2].length) (baseStart_298035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298035 prefixEnd_298035 := by exact prefixLift 298035
  have htrace : WordTrace (prefixWord ++ tailWord_298035) baseStart_298035 baseEnd_298035 := by
    simpa [prefixWord, tailWord_298035, baseEnd_298035] using wordTrace_append hprefix tailTrace_298035
  have hstable : (prefixWord ++ tailWord_298035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298035).length < 2 ^ (prefixWord ++ tailWord_298035).sum := by decide
  have hdescent : baseEnd_298035 < baseStart_298035 := by decide
  rcases family_descends (prefixWord ++ tailWord_298035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298056 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 4]
def baseStart_298056 : Nat := 118140960795 + 298056 * 2 ^ 59
def prefixEnd_298056 : Nat := 4983230072969 + 3 ^ 40 * 298056 * 2
def baseEnd_298056 : Nat := 136040879961414300648241

theorem tailTrace_298056 : CollatzResearch.WordTrace tailWord_298056 prefixEnd_298056 136040879961414300648241 := by
  unfold tailWord_298056
  simp only [CollatzResearch.WordTrace]
  refine ⟨5435497704100745378621011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7247330272134327171494681 5435497704100745378621011)
  ·
    refine ⟨8153246556151118067931517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5435497704100745378621011 8153246556151118067931517)
    ·
      refine ⟨3057467458556669275474319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8153246556151118067931517 3057467458556669275474319)
      ·
        refine ⟨4586201187835003913211479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3057467458556669275474319 4586201187835003913211479)
        ·
          refine ⟨6879301781752505869817219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4586201187835003913211479 6879301781752505869817219)
          ·
            refine ⟨10318952672628758804725829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6879301781752505869817219 10318952672628758804725829)
            ·
              refine ⟨1934803626117892275886093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10318952672628758804725829 1934803626117892275886093)
              ·
                refine ⟨725551359794209603457285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1934803626117892275886093 725551359794209603457285)
                ·
                  refine ⟨136040879961414300648241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 725551359794209603457285 136040879961414300648241)
                  ·
                    rfl

theorem cell20_298056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_298056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298056 prefixEnd_298056 := by exact prefixLift 298056
  have htrace : WordTrace (prefixWord ++ tailWord_298056) baseStart_298056 baseEnd_298056 := by
    simpa [prefixWord, tailWord_298056, baseEnd_298056] using wordTrace_append hprefix tailTrace_298056
  have hstable : (prefixWord ++ tailWord_298056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298056).length < 2 ^ (prefixWord ++ tailWord_298056).sum := by decide
  have hdescent : baseEnd_298056 < baseStart_298056 := by decide
  rcases family_descends (prefixWord ++ tailWord_298056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298066 : List Nat := [3, 2, 2, 1, 3, 1, 2, 3, 3]
def baseStart_298066 : Nat := 118140960795 + 298066 * 2 ^ 59
def prefixEnd_298066 : Nat := 4983230072969 + 3 ^ 40 * 298066 * 2
def baseEnd_298066 : Nat := 136045444233898710314867

theorem tailTrace_298066 : CollatzResearch.WordTrace tailWord_298066 prefixEnd_298066 136045444233898710314867 := by
  unfold tailWord_298066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2717840034541315616276513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7247573425443508310070701 2717840034541315616276513)
  ·
    refine ⟨2038380025905986712207385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2717840034541315616276513 2038380025905986712207385)
    ·
      refine ⟨1528785019429490034155539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2038380025905986712207385 1528785019429490034155539)
      ·
        refine ⟨2293177529144235051233309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1528785019429490034155539 2293177529144235051233309)
        ·
          refine ⟨859941573429088144212491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2293177529144235051233309 859941573429088144212491)
          ·
            refine ⟨1289912360143632216318737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859941573429088144212491 1289912360143632216318737)
            ·
              refine ⟨967434270107724162239053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1289912360143632216318737 967434270107724162239053)
              ·
                refine ⟨362787851290396560839645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 967434270107724162239053 362787851290396560839645)
                ·
                  refine ⟨136045444233898710314867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362787851290396560839645 136045444233898710314867)
                  ·
                    rfl

theorem cell20_298066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_298066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298066 prefixEnd_298066 := by exact prefixLift 298066
  have htrace : WordTrace (prefixWord ++ tailWord_298066) baseStart_298066 baseEnd_298066 := by
    simpa [prefixWord, tailWord_298066, baseEnd_298066] using wordTrace_append hprefix tailTrace_298066
  have hstable : (prefixWord ++ tailWord_298066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298066).length < 2 ^ (prefixWord ++ tailWord_298066).sum := by decide
  have hdescent : baseEnd_298066 < baseStart_298066 := by decide
  rcases family_descends (prefixWord ++ tailWord_298066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298080 : List Nat := [2, 1, 1, 3, 2, 2, 5, 4]
def baseStart_298080 : Nat := 118140960795 + 298080 * 2 ^ 59
def prefixEnd_298080 : Nat := 4983230072969 + 3 ^ 40 * 298080 * 2
def baseEnd_298080 : Nat := 45350611405125627949381

theorem tailTrace_298080 : CollatzResearch.WordTrace tailWord_298080 prefixEnd_298080 45350611405125627949381 := by
  unfold tailWord_298080
  simp only [CollatzResearch.WordTrace]
  refine ⟨5435935380057271428057847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7247913840076361904077129 5435935380057271428057847)
  ·
    refine ⟨8153903070085907142086771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5435935380057271428057847 8153903070085907142086771)
    ·
      refine ⟨12230854605128860713130157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8153903070085907142086771 12230854605128860713130157)
      ·
        refine ⟨4586570476923322767423809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12230854605128860713130157 4586570476923322767423809)
        ·
          refine ⟨3439927857692492075567857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4586570476923322767423809 3439927857692492075567857)
          ·
            refine ⟨2579945893269369056675893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3439927857692492075567857 2579945893269369056675893)
            ·
              refine ⟨241869927494003349063365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2579945893269369056675893 241869927494003349063365)
              ·
                refine ⟨45350611405125627949381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241869927494003349063365 45350611405125627949381)
                ·
                  rfl

theorem cell20_298080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_298080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298080 prefixEnd_298080 := by exact prefixLift 298080
  have htrace : WordTrace (prefixWord ++ tailWord_298080) baseStart_298080 baseEnd_298080 := by
    simpa [prefixWord, tailWord_298080, baseEnd_298080] using wordTrace_append hprefix tailTrace_298080
  have hstable : (prefixWord ++ tailWord_298080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298080).length < 2 ^ (prefixWord ++ tailWord_298080).sum := by decide
  have hdescent : baseEnd_298080 < baseStart_298080 := by decide
  rcases family_descends (prefixWord ++ tailWord_298080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298090 : List Nat := [3, 1, 3, 2, 2, 1, 1, 5, 2]
def baseStart_298090 : Nat := 118140960795 + 298090 * 2 ^ 59
def prefixEnd_298090 : Nat := 4983230072969 + 3 ^ 40 * 298090 * 2
def baseEnd_298090 : Nat := 136056398487861293514769

theorem tailTrace_298090 : CollatzResearch.WordTrace tailWord_298090 prefixEnd_298090 136056398487861293514769 := by
  unfold tailWord_298090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2718058872519578640994931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7248156993385543042653149 2718058872519578640994931)
  ·
    refine ⟨4077088308779367961492397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2718058872519578640994931 4077088308779367961492397)
    ·
      refine ⟨1528908115792262985559649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4077088308779367961492397 1528908115792262985559649)
      ·
        refine ⟨1146681086844197239169737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1528908115792262985559649 1146681086844197239169737)
        ·
          refine ⟨860010815133147929377303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1146681086844197239169737 860010815133147929377303)
          ·
            refine ⟨1290016222699721894065955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860010815133147929377303 1290016222699721894065955)
            ·
              refine ⟨1935024334049582841098933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1290016222699721894065955 1935024334049582841098933)
              ·
                refine ⟨181408531317148391353025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1935024334049582841098933 181408531317148391353025)
                ·
                  refine ⟨136056398487861293514769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181408531317148391353025 136056398487861293514769)
                  ·
                    rfl

theorem cell20_298090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_298090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298090 prefixEnd_298090 := by exact prefixLift 298090
  have htrace : WordTrace (prefixWord ++ tailWord_298090) baseStart_298090 baseEnd_298090 := by
    simpa [prefixWord, tailWord_298090, baseEnd_298090] using wordTrace_append hprefix tailTrace_298090
  have hstable : (prefixWord ++ tailWord_298090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298090).length < 2 ^ (prefixWord ++ tailWord_298090).sum := by decide
  have hdescent : baseEnd_298090 < baseStart_298090 := by decide
  rcases family_descends (prefixWord ++ tailWord_298090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298135 : List Nat := [1, 1, 3, 3, 3, 3, 2, 4]
def baseStart_298135 : Nat := 118140960795 + 298135 * 2 ^ 59
def prefixEnd_298135 : Nat := 4983230072969 + 3 ^ 40 * 298135 * 2
def baseEnd_298135 : Nat := 45358979238013712338195

theorem tailTrace_298135 : CollatzResearch.WordTrace tailWord_298135 prefixEnd_298135 45358979238013712338195 := by
  unfold tailWord_298135
  simp only [CollatzResearch.WordTrace]
  refine ⟨10873876774915287249367859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7249251183276858166245239 10873876774915287249367859)
  ·
    refine ⟨16310815162372930874051789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10873876774915287249367859 16310815162372930874051789)
    ·
      refine ⟨6116555685889849077769421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16310815162372930874051789 6116555685889849077769421)
      ·
        refine ⟨2293708382208693404163533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6116555685889849077769421 2293708382208693404163533)
        ·
          refine ⟨860140643328260026561325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2293708382208693404163533 860140643328260026561325)
          ·
            refine ⟨322552741248097509960497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 860140643328260026561325 322552741248097509960497)
            ·
              refine ⟨241914555936073132470373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322552741248097509960497 241914555936073132470373)
              ·
                refine ⟨45358979238013712338195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 241914555936073132470373 45358979238013712338195)
                ·
                  rfl

theorem cell20_298135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 4].length) (baseStart_298135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298135 prefixEnd_298135 := by exact prefixLift 298135
  have htrace : WordTrace (prefixWord ++ tailWord_298135) baseStart_298135 baseEnd_298135 := by
    simpa [prefixWord, tailWord_298135, baseEnd_298135] using wordTrace_append hprefix tailTrace_298135
  have hstable : (prefixWord ++ tailWord_298135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298135).length < 2 ^ (prefixWord ++ tailWord_298135).sum := by decide
  have hdescent : baseEnd_298135 < baseStart_298135 := by decide
  rcases family_descends (prefixWord ++ tailWord_298135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298142 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_298142 : Nat := 118140960795 + 298142 * 2 ^ 59
def prefixEnd_298142 : Nat := 4983230072969 + 3 ^ 40 * 298142 * 2
def baseEnd_298142 : Nat := 136080132704780223781223

theorem tailTrace_298142 : CollatzResearch.WordTrace tailWord_298142 prefixEnd_298142 136080132704780223781223 := by
  unfold tailWord_298142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1359266510736240930609085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7249421390593284963248453 1359266510736240930609085)
  ·
    refine ⟨509724941526090348978407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1359266510736240930609085 509724941526090348978407)
    ·
      refine ⟨764587412289135523467611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 509724941526090348978407 764587412289135523467611)
      ·
        refine ⟨1146881118433703285201417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 764587412289135523467611 1146881118433703285201417)
        ·
          refine ⟨860160838825277463901063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1146881118433703285201417 860160838825277463901063)
          ·
            refine ⟨1290241258237916195851595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860160838825277463901063 1290241258237916195851595)
            ·
              refine ⟨1935361887356874293777393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1290241258237916195851595 1935361887356874293777393)
              ·
                refine ⟨1451521415517655720333045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1935361887356874293777393 1451521415517655720333045)
                ·
                  refine ⟨136080132704780223781223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1451521415517655720333045 136080132704780223781223)
                  ·
                    rfl

theorem cell20_298142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_298142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298142 prefixEnd_298142 := by exact prefixLift 298142
  have htrace : WordTrace (prefixWord ++ tailWord_298142) baseStart_298142 baseEnd_298142 := by
    simpa [prefixWord, tailWord_298142, baseEnd_298142] using wordTrace_append hprefix tailTrace_298142
  have hstable : (prefixWord ++ tailWord_298142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298142).length < 2 ^ (prefixWord ++ tailWord_298142).sum := by decide
  have hdescent : baseEnd_298142 < baseStart_298142 := by decide
  rcases family_descends (prefixWord ++ tailWord_298142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298176 : List Nat := [2, 1, 1, 2, 7, 1, 2, 1, 3]
def baseStart_298176 : Nat := 118140960795 + 298176 * 2 ^ 59
def prefixEnd_298176 : Nat := 4983230072969 + 3 ^ 40 * 298176 * 2
def baseEnd_298176 : Nat := 136095651231227216647751

theorem tailTrace_298176 : CollatzResearch.WordTrace tailWord_298176 prefixEnd_298176 136095651231227216647751 := by
  unfold tailWord_298176
  simp only [CollatzResearch.WordTrace]
  refine ⟨5437686083883375625805191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7250248111844500834406921 5437686083883375625805191)
  ·
    refine ⟨8156529125825063438707787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5437686083883375625805191 8156529125825063438707787)
    ·
      refine ⟨12234793688737595158061681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8156529125825063438707787 12234793688737595158061681)
      ·
        refine ⟨9176095266553196368546261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12234793688737595158061681 9176095266553196368546261)
        ·
          refine ⟨215064732809840539887803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9176095266553196368546261 215064732809840539887803)
          ·
            refine ⟨322597099214760809831705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215064732809840539887803 322597099214760809831705)
            ·
              refine ⟨241947824411070607373779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322597099214760809831705 241947824411070607373779)
              ·
                refine ⟨362921736616605911060669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241947824411070607373779 362921736616605911060669)
                ·
                  refine ⟨136095651231227216647751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362921736616605911060669 136095651231227216647751)
                  ·
                    rfl

theorem cell20_298176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 3].length) (baseStart_298176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298176 prefixEnd_298176 := by exact prefixLift 298176
  have htrace : WordTrace (prefixWord ++ tailWord_298176) baseStart_298176 baseEnd_298176 := by
    simpa [prefixWord, tailWord_298176, baseEnd_298176] using wordTrace_append hprefix tailTrace_298176
  have hstable : (prefixWord ++ tailWord_298176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298176).length < 2 ^ (prefixWord ++ tailWord_298176).sum := by decide
  have hdescent : baseEnd_298176 < baseStart_298176 := by decide
  rcases family_descends (prefixWord ++ tailWord_298176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298215 : List Nat := [1, 1, 5, 3, 10]
def baseStart_298215 : Nat := 118140960795 + 298215 * 2 ^ 59
def prefixEnd_298215 : Nat := 4983230072969 + 3 ^ 40 * 298215 * 2
def baseEnd_298215 : Nat := 1680412986344647090711

theorem tailTrace_298215 : CollatzResearch.WordTrace tailWord_298215 prefixEnd_298215 1680412986344647090711 := by
  unfold tailWord_298215
  simp only [CollatzResearch.WordTrace]
  refine ⟨10876794614625460912280099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7251196409750307274853399 10876794614625460912280099)
  ·
    refine ⟨16315191921938191368420149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10876794614625460912280099 16315191921938191368420149)
    ·
      refine ⟨1529549242681705440789389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16315191921938191368420149 1529549242681705440789389)
      ·
        refine ⟨573580966005639540296021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1529549242681705440789389 573580966005639540296021)
        ·
          refine ⟨1680412986344647090711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 573580966005639540296021 1680412986344647090711)
          ·
            rfl

theorem cell20_298215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 10].length) (baseStart_298215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298215 prefixEnd_298215 := by exact prefixLift 298215
  have htrace : WordTrace (prefixWord ++ tailWord_298215) baseStart_298215 baseEnd_298215 := by
    simpa [prefixWord, tailWord_298215, baseEnd_298215] using wordTrace_append hprefix tailTrace_298215
  have hstable : (prefixWord ++ tailWord_298215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298215).length < 2 ^ (prefixWord ++ tailWord_298215).sum := by decide
  have hdescent : baseEnd_298215 < baseStart_298215 := by decide
  rcases family_descends (prefixWord ++ tailWord_298215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298218 : List Nat := [3, 1, 3, 1, 1, 4, 2, 2, 3]
def baseStart_298218 : Nat := 118140960795 + 298218 * 2 ^ 59
def prefixEnd_298218 : Nat := 4983230072969 + 3 ^ 40 * 298218 * 2
def baseEnd_298218 : Nat := 136114821175661737247579

theorem tailTrace_298218 : CollatzResearch.WordTrace tailWord_298218 prefixEnd_298218 136114821175661737247579 := by
  unfold tailWord_298218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2719226008403648106159827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7251269355743061616426205 2719226008403648106159827)
  ·
    refine ⟨4078839012605472159239741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2719226008403648106159827 4078839012605472159239741)
    ·
      refine ⟨1529564629727052059714903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4078839012605472159239741 1529564629727052059714903)
      ·
        refine ⟨2294346944590578089572355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1529564629727052059714903 2294346944590578089572355)
        ·
          refine ⟨3441520416885867134358533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2294346944590578089572355 3441520416885867134358533)
          ·
            refine ⟨645285078166100087692225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3441520416885867134358533 645285078166100087692225)
            ·
              refine ⟨483963808624575065769169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 645285078166100087692225 483963808624575065769169)
              ·
                refine ⟨362972856468431299326877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 483963808624575065769169 362972856468431299326877)
                ·
                  refine ⟨136114821175661737247579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362972856468431299326877 136114821175661737247579)
                  ·
                    rfl

theorem cell20_298218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_298218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_298218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_298218 prefixEnd_298218 := by exact prefixLift 298218
  have htrace : WordTrace (prefixWord ++ tailWord_298218) baseStart_298218 baseEnd_298218 := by
    simpa [prefixWord, tailWord_298218, baseEnd_298218] using wordTrace_append hprefix tailTrace_298218
  have hstable : (prefixWord ++ tailWord_298218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298218).length < 2 ^ (prefixWord ++ tailWord_298218).sum := by decide
  have hdescent : baseEnd_298218 < baseStart_298218 := by decide
  rcases family_descends (prefixWord ++ tailWord_298218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
