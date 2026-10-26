import V185TrunkScan20Chunk064

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_396327 : List Nat := [1, 1, 7, 1, 1, 2, 2, 3, 2]
def baseStart_396327 : Nat := 118140960795 + 396327 * 2 ^ 59
def prefixEnd_396327 : Nat := 4983230072969 + 3 ^ 40 * 396327 * 2
def baseEnd_396327 : Nat := 180894442092956535546517

theorem tailTrace_396327 : CollatzResearch.WordTrace tailWord_396327 prefixEnd_396327 180894442092956535546517 := by
  unfold tailWord_396327
  simp only [CollatzResearch.WordTrace]
  refine ⟨14455233235182441107851235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9636822156788294071900823 14455233235182441107851235)
  ·
    refine ⟨21682849852773661661776853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14455233235182441107851235 21682849852773661661776853)
    ·
      refine ⟨508191793424382695197895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 21682849852773661661776853 508191793424382695197895)
      ·
        refine ⟨762287690136574042796843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508191793424382695197895 762287690136574042796843)
        ·
          refine ⟨1143431535204861064195265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762287690136574042796843 1143431535204861064195265)
          ·
            refine ⟨857573651403645798146449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1143431535204861064195265 857573651403645798146449)
            ·
              refine ⟨643180238552734348609837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857573651403645798146449 643180238552734348609837)
              ·
                refine ⟨241192589457275380728689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 643180238552734348609837 241192589457275380728689)
                ·
                  refine ⟨180894442092956535546517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241192589457275380728689 180894442092956535546517)
                  ·
                    rfl

theorem cell20_396327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 2].length) (baseStart_396327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396327 prefixEnd_396327 := by exact prefixLift 396327
  have htrace : WordTrace (prefixWord ++ tailWord_396327) baseStart_396327 baseEnd_396327 := by
    simpa [prefixWord, tailWord_396327, baseEnd_396327] using wordTrace_append hprefix tailTrace_396327
  have hstable : (prefixWord ++ tailWord_396327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396327).length < 2 ^ (prefixWord ++ tailWord_396327).sum := by decide
  have hdescent : baseEnd_396327 < baseStart_396327 := by decide
  rcases family_descends (prefixWord ++ tailWord_396327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396331 : List Nat := [1, 1, 1, 1, 2, 1, 8, 3, 2]
def baseStart_396331 : Nat := 118140960795 + 396331 * 2 ^ 59
def prefixEnd_396331 : Nat := 4983230072969 + 3 ^ 40 * 396331 * 2
def baseEnd_396331 : Nat := 180896267801950299413167

theorem tailTrace_396331 : CollatzResearch.WordTrace tailWord_396331 prefixEnd_396331 180896267801950299413167 := by
  unfold tailWord_396331
  simp only [CollatzResearch.WordTrace]
  refine ⟨14455379127167949790996847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9636919418111966527331231 14455379127167949790996847)
  ·
    refine ⟨21683068690751924686495271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14455379127167949790996847 21683068690751924686495271)
    ·
      refine ⟨32524603036127887029742907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21683068690751924686495271 32524603036127887029742907)
      ·
        refine ⟨48786904554191830544614361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32524603036127887029742907 48786904554191830544614361)
        ·
          refine ⟨36590178415643872908460771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48786904554191830544614361 36590178415643872908460771)
          ·
            refine ⟨54885267623465809362691157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36590178415643872908460771 54885267623465809362691157)
            ·
              refine ⟨643186729962489953469037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 54885267623465809362691157 643186729962489953469037)
              ·
                refine ⟨241195023735933732550889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 643186729962489953469037 241195023735933732550889)
                ·
                  refine ⟨180896267801950299413167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241195023735933732550889 180896267801950299413167)
                  ·
                    rfl

theorem cell20_396331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 2].length) (baseStart_396331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396331 prefixEnd_396331 := by exact prefixLift 396331
  have htrace : WordTrace (prefixWord ++ tailWord_396331) baseStart_396331 baseEnd_396331 := by
    simpa [prefixWord, tailWord_396331, baseEnd_396331] using wordTrace_append hprefix tailTrace_396331
  have hstable : (prefixWord ++ tailWord_396331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396331).length < 2 ^ (prefixWord ++ tailWord_396331).sum := by decide
  have hdescent : baseEnd_396331 < baseStart_396331 := by decide
  rcases family_descends (prefixWord ++ tailWord_396331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396345 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 5]
def baseStart_396345 : Nat := 118140960795 + 396345 * 2 ^ 59
def prefixEnd_396345 : Nat := 4983230072969 + 3 ^ 40 * 396345 * 2
def baseEnd_396345 : Nat := 180902657783428472946443

theorem tailTrace_396345 : CollatzResearch.WordTrace tailWord_396345 prefixEnd_396345 180902657783428472946443 := by
  unfold tailWord_396345
  simp only [CollatzResearch.WordTrace]
  refine ⟨14455889749117230182006489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9637259832744820121337659 14455889749117230182006489)
  ·
    refine ⟨10841917311837922636504867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14455889749117230182006489 10841917311837922636504867)
    ·
      refine ⟨16262875967756883954757301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10841917311837922636504867 16262875967756883954757301)
      ·
        refine ⟨1524644621977207870758497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16262875967756883954757301 1524644621977207870758497)
        ·
          refine ⟨1143483466482905903068873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1524644621977207870758497 1143483466482905903068873)
          ·
            refine ⟨857612599862179427301655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1143483466482905903068873 857612599862179427301655)
            ·
              refine ⟨1286418899793269140952483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857612599862179427301655 1286418899793269140952483)
              ·
                refine ⟨1929628349689903711428725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1286418899793269140952483 1929628349689903711428725)
                ·
                  refine ⟨180902657783428472946443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1929628349689903711428725 180902657783428472946443)
                  ·
                    rfl

theorem cell20_396345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_396345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396345 prefixEnd_396345 := by exact prefixLift 396345
  have htrace : WordTrace (prefixWord ++ tailWord_396345) baseStart_396345 baseEnd_396345 := by
    simpa [prefixWord, tailWord_396345, baseEnd_396345] using wordTrace_append hprefix tailTrace_396345
  have hstable : (prefixWord ++ tailWord_396345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396345).length < 2 ^ (prefixWord ++ tailWord_396345).sum := by decide
  have hdescent : baseEnd_396345 < baseStart_396345 := by decide
  rcases family_descends (prefixWord ++ tailWord_396345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396352 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 4]
def baseStart_396352 : Nat := 118140960795 + 396352 * 2 ^ 59
def prefixEnd_396352 : Nat := 4983230072969 + 3 ^ 40 * 396352 * 2
def baseEnd_396352 : Nat := 180905852774167559713081

theorem tailTrace_396352 : CollatzResearch.WordTrace tailWord_396352 prefixEnd_396352 180905852774167559713081 := by
  unfold tailWord_396352
  simp only [CollatzResearch.WordTrace]
  refine ⟨7228072530045935188755655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9637430040061246918340873 7228072530045935188755655)
  ·
    refine ⟨10842108795068902783133483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7228072530045935188755655 10842108795068902783133483)
    ·
      refine ⟨16263163192603354174700225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10842108795068902783133483 16263163192603354174700225)
      ·
        refine ⟨12197372394452515631025169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16263163192603354174700225 12197372394452515631025169)
        ·
          refine ⟨9148029295839386723268877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12197372394452515631025169 9148029295839386723268877)
          ·
            refine ⟨3430510985939770021225829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9148029295839386723268877 3430510985939770021225829)
            ·
              refine ⟨643220809863706878979843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3430510985939770021225829 643220809863706878979843)
              ·
                refine ⟨964831214795560318469765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643220809863706878979843 964831214795560318469765)
                ·
                  refine ⟨180905852774167559713081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 964831214795560318469765 180905852774167559713081)
                  ·
                    rfl

theorem cell20_396352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_396352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396352 prefixEnd_396352 := by exact prefixLift 396352
  have htrace : WordTrace (prefixWord ++ tailWord_396352) baseStart_396352 baseEnd_396352 := by
    simpa [prefixWord, tailWord_396352, baseEnd_396352] using wordTrace_append hprefix tailTrace_396352
  have hstable : (prefixWord ++ tailWord_396352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396352).length < 2 ^ (prefixWord ++ tailWord_396352).sum := by decide
  have hdescent : baseEnd_396352 < baseStart_396352 := by decide
  rcases family_descends (prefixWord ++ tailWord_396352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396358 : List Nat := [6, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_396358 : Nat := 118140960795 + 396358 * 2 ^ 59
def prefixEnd_396358 : Nat := 4983230072969 + 3 ^ 40 * 396358 * 2
def baseEnd_396358 : Nat := 180908591337658205513057

theorem tailTrace_396358 : CollatzResearch.WordTrace tailWord_396358 prefixEnd_396358 180908591337658205513057 := by
  unfold tailWord_396358
  simp only [CollatzResearch.WordTrace]
  refine ⟨451761371814691668819679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9637575932046755601486485 451761371814691668819679)
  ·
    refine ⟨677642057722037503229519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 451761371814691668819679 677642057722037503229519)
    ·
      refine ⟨1016463086583056254844279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 677642057722037503229519 1016463086583056254844279)
      ·
        refine ⟨1524694629874584382266419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016463086583056254844279 1524694629874584382266419)
        ·
          refine ⟨2287041944811876573399629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524694629874584382266419 2287041944811876573399629)
          ·
            refine ⟨857640729304453715024861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2287041944811876573399629 857640729304453715024861)
            ·
              refine ⟨321615273489170143134323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 857640729304453715024861 321615273489170143134323)
              ·
                refine ⟨482422910233755214701485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321615273489170143134323 482422910233755214701485)
                ·
                  refine ⟨180908591337658205513057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 482422910233755214701485 180908591337658205513057)
                  ·
                    rfl

theorem cell20_396358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_396358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396358 prefixEnd_396358 := by exact prefixLift 396358
  have htrace : WordTrace (prefixWord ++ tailWord_396358) baseStart_396358 baseEnd_396358 := by
    simpa [prefixWord, tailWord_396358, baseEnd_396358] using wordTrace_append hprefix tailTrace_396358
  have hstable : (prefixWord ++ tailWord_396358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396358).length < 2 ^ (prefixWord ++ tailWord_396358).sum := by decide
  have hdescent : baseEnd_396358 < baseStart_396358 := by decide
  rcases family_descends (prefixWord ++ tailWord_396358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396382 : List Nat := [4, 4, 1, 1, 1, 1, 3, 3, 2]
def baseStart_396382 : Nat := 118140960795 + 396382 * 2 ^ 59
def prefixEnd_396382 : Nat := 4983230072969 + 3 ^ 40 * 396382 * 2
def baseEnd_396382 : Nat := 180919545591620788712959

theorem tailTrace_396382 : CollatzResearch.WordTrace tailWord_396382 prefixEnd_396382 180919545591620788712959 := by
  unfold tailWord_396382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1807154906247898187637925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9638159499988790334068933 1807154906247898187637925)
  ·
    refine ⟨338841544921480910182111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1807154906247898187637925 338841544921480910182111)
    ·
      refine ⟨508262317382221365273167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338841544921480910182111 508262317382221365273167)
      ·
        refine ⟨762393476073332047909751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508262317382221365273167 762393476073332047909751)
        ·
          refine ⟨1143590214109998071864627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762393476073332047909751 1143590214109998071864627)
          ·
            refine ⟨1715385321164997107796941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143590214109998071864627 1715385321164997107796941)
            ·
              refine ⟨643269495436873915423853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1715385321164997107796941 643269495436873915423853)
              ·
                refine ⟨241226060788827718283945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 643269495436873915423853 241226060788827718283945)
                ·
                  refine ⟨180919545591620788712959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241226060788827718283945 180919545591620788712959)
                  ·
                    rfl

theorem cell20_396382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_396382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396382 prefixEnd_396382 := by exact prefixLift 396382
  have htrace : WordTrace (prefixWord ++ tailWord_396382) baseStart_396382 baseEnd_396382 := by
    simpa [prefixWord, tailWord_396382, baseEnd_396382] using wordTrace_append hprefix tailTrace_396382
  have hstable : (prefixWord ++ tailWord_396382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396382).length < 2 ^ (prefixWord ++ tailWord_396382).sum := by decide
  have hdescent : baseEnd_396382 < baseStart_396382 := by decide
  rcases family_descends (prefixWord ++ tailWord_396382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396397 : List Nat := [1, 5, 1, 1, 2, 2, 8]
def baseStart_396397 : Nat := 118140960795 + 396397 * 2 ^ 59
def prefixEnd_396397 : Nat := 4983230072969 + 3 ^ 40 * 396397 * 2
def baseEnd_396397 : Nat := 20102932444483044801433

theorem tailTrace_396397 : CollatzResearch.WordTrace tailWord_396397 prefixEnd_396397 20102932444483044801433 := by
  unfold tailWord_396397
  simp only [CollatzResearch.WordTrace]
  refine ⟨14457786344928843062899445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9638524229952562041932963 14457786344928843062899445)
  ·
    refine ⟨1355417469837079037146823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14457786344928843062899445 1355417469837079037146823)
    ·
      refine ⟨2033126204755618555720235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1355417469837079037146823 2033126204755618555720235)
      ·
        refine ⟨3049689307133427833580353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2033126204755618555720235 3049689307133427833580353)
        ·
          refine ⟨2287266980350070875185265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3049689307133427833580353 2287266980350070875185265)
          ·
            refine ⟨1715450235262553156388949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2287266980350070875185265 1715450235262553156388949)
            ·
              refine ⟨20102932444483044801433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1715450235262553156388949 20102932444483044801433)
              ·
                rfl

theorem cell20_396397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 8].length) (baseStart_396397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396397 prefixEnd_396397 := by exact prefixLift 396397
  have htrace : WordTrace (prefixWord ++ tailWord_396397) baseStart_396397 baseEnd_396397 := by
    simpa [prefixWord, tailWord_396397, baseEnd_396397] using wordTrace_append hprefix tailTrace_396397
  have hstable : (prefixWord ++ tailWord_396397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396397).length < 2 ^ (prefixWord ++ tailWord_396397).sum := by decide
  have hdescent : baseEnd_396397 < baseStart_396397 := by decide
  rcases family_descends (prefixWord ++ tailWord_396397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396417 : List Nat := [1, 2, 4, 2, 2, 3, 2, 1, 3]
def baseStart_396417 : Nat := 118140960795 + 396417 * 2 ^ 59
def prefixEnd_396417 : Nat := 4983230072969 + 3 ^ 40 * 396417 * 2
def baseEnd_396417 : Nat := 180935520545316222546149

theorem tailTrace_396417 : CollatzResearch.WordTrace tailWord_396417 prefixEnd_396417 180935520545316222546149 := by
  unfold tailWord_396417
  simp only [CollatzResearch.WordTrace]
  refine ⟨14458515804856386478627505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9639010536570924319085003 14458515804856386478627505)
  ·
    refine ⟨10843886853642289858970629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14458515804856386478627505 10843886853642289858970629)
    ·
      refine ⟨2033228785057929348556993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10843886853642289858970629 2033228785057929348556993)
      ·
        refine ⟨1524921588793447011417745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2033228785057929348556993 1524921588793447011417745)
        ·
          refine ⟨1143691191595085258563309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1524921588793447011417745 1143691191595085258563309)
          ·
            refine ⟨428884196848156971961241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1143691191595085258563309 428884196848156971961241)
            ·
              refine ⟨321663147636117728970931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428884196848156971961241 321663147636117728970931)
              ·
                refine ⟨482494721454176593456397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321663147636117728970931 482494721454176593456397)
                ·
                  refine ⟨180935520545316222546149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 482494721454176593456397 180935520545316222546149)
                  ·
                    rfl

theorem cell20_396417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_396417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396417 prefixEnd_396417 := by exact prefixLift 396417
  have htrace : WordTrace (prefixWord ++ tailWord_396417) baseStart_396417 baseEnd_396417 := by
    simpa [prefixWord, tailWord_396417, baseEnd_396417] using wordTrace_append hprefix tailTrace_396417
  have hstable : (prefixWord ++ tailWord_396417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396417).length < 2 ^ (prefixWord ++ tailWord_396417).sum := by decide
  have hdescent : baseEnd_396417 < baseStart_396417 := by decide
  rcases family_descends (prefixWord ++ tailWord_396417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396445 : List Nat := [1, 4, 2, 1, 1, 2, 2, 5, 2]
def baseStart_396445 : Nat := 118140960795 + 396445 * 2 ^ 59
def prefixEnd_396445 : Nat := 4983230072969 + 3 ^ 40 * 396445 * 2
def baseEnd_396445 : Nat := 180948300508272569612701

theorem tailTrace_396445 : CollatzResearch.WordTrace tailWord_396445 prefixEnd_396445 180948300508272569612701 := by
  unfold tailWord_396445
  simp only [CollatzResearch.WordTrace]
  refine ⟨14459537048754947260646789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9639691365836631507097859 14459537048754947260646789)
  ·
    refine ⟨2711163196641552611371273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14459537048754947260646789 2711163196641552611371273)
    ·
      refine ⟨2033372397481164458528455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2711163196641552611371273 2033372397481164458528455)
      ·
        refine ⟨3050058596221746687792683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2033372397481164458528455 3050058596221746687792683)
        ·
          refine ⟨4575087894332620031689025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3050058596221746687792683 4575087894332620031689025)
          ·
            refine ⟨3431315920749465023766769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4575087894332620031689025 3431315920749465023766769)
            ·
              refine ⟨2573486940562098767825077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3431315920749465023766769 2573486940562098767825077)
              ·
                refine ⟨241264400677696759483601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2573486940562098767825077 241264400677696759483601)
                ·
                  refine ⟨180948300508272569612701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241264400677696759483601 180948300508272569612701)
                  ·
                    rfl

theorem cell20_396445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_396445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396445 prefixEnd_396445 := by exact prefixLift 396445
  have htrace : WordTrace (prefixWord ++ tailWord_396445) baseStart_396445 baseEnd_396445 := by
    simpa [prefixWord, tailWord_396445, baseEnd_396445] using wordTrace_append hprefix tailTrace_396445
  have hstable : (prefixWord ++ tailWord_396445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396445).length < 2 ^ (prefixWord ++ tailWord_396445).sum := by decide
  have hdescent : baseEnd_396445 < baseStart_396445 := by decide
  rcases family_descends (prefixWord ++ tailWord_396445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396456 : List Nat := [2, 1, 17]
def baseStart_396456 : Nat := 118140960795 + 396456 * 2 ^ 59
def prefixEnd_396456 : Nat := 4983230072969 + 3 ^ 40 * 396456 * 2
def baseEnd_396456 : Nat := 248221291094657640941

theorem tailTrace_396456 : CollatzResearch.WordTrace tailWord_396456 prefixEnd_396456 248221291094657640941 := by
  unfold tailWord_396456
  simp only [CollatzResearch.WordTrace]
  refine ⟨7229969125857548069648611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9639958834476730759531481 7229969125857548069648611)
  ·
    refine ⟨10844953688786322104472917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7229969125857548069648611 10844953688786322104472917)
    ·
      refine ⟨248221291094657640941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 17 10844953688786322104472917 248221291094657640941)
      ·
        rfl

theorem cell20_396456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 17].length) (baseStart_396456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396456 prefixEnd_396456 := by exact prefixLift 396456
  have htrace : WordTrace (prefixWord ++ tailWord_396456) baseStart_396456 baseEnd_396456 := by
    simpa [prefixWord, tailWord_396456, baseEnd_396456] using wordTrace_append hprefix tailTrace_396456
  have hstable : (prefixWord ++ tailWord_396456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396456).length < 2 ^ (prefixWord ++ tailWord_396456).sum := by decide
  have hdescent : baseEnd_396456 < baseStart_396456 := by decide
  rcases family_descends (prefixWord ++ tailWord_396456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396458 : List Nat := [3, 1, 5, 1, 1, 3, 2, 2, 2]
def baseStart_396458 : Nat := 118140960795 + 396458 * 2 ^ 59
def prefixEnd_396458 : Nat := 4983230072969 + 3 ^ 40 * 396458 * 2
def baseEnd_396458 : Nat := 180954234062502302179315

theorem tailTrace_396458 : CollatzResearch.WordTrace tailWord_396458 prefixEnd_396458 180954234062502302179315 := by
  unfold tailWord_396458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3615002799426962620217507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9640007465138566987246685 3615002799426962620217507)
  ·
    refine ⟨5422504199140443930326261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3615002799426962620217507 5422504199140443930326261)
    ·
      refine ⟨508359768669416618468087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5422504199140443930326261 508359768669416618468087)
      ·
        refine ⟨762539653004124927702131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508359768669416618468087 762539653004124927702131)
        ·
          refine ⟨1143809479506187391553197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762539653004124927702131 1143809479506187391553197)
          ·
            refine ⟨428928554814820271832449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1143809479506187391553197 428928554814820271832449)
            ·
              refine ⟨321696416111115203874337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428928554814820271832449 321696416111115203874337)
              ·
                refine ⟨241272312083336402905753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321696416111115203874337 241272312083336402905753)
                ·
                  refine ⟨180954234062502302179315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241272312083336402905753 180954234062502302179315)
                  ·
                    rfl

theorem cell20_396458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_396458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396458 prefixEnd_396458 := by exact prefixLift 396458
  have htrace : WordTrace (prefixWord ++ tailWord_396458) baseStart_396458 baseEnd_396458 := by
    simpa [prefixWord, tailWord_396458, baseEnd_396458] using wordTrace_append hprefix tailTrace_396458
  have hstable : (prefixWord ++ tailWord_396458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396458).length < 2 ^ (prefixWord ++ tailWord_396458).sum := by decide
  have hdescent : baseEnd_396458 < baseStart_396458 := by decide
  rcases family_descends (prefixWord ++ tailWord_396458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396473 : List Nat := [1, 2, 1, 4, 1, 3, 3, 5]
def baseStart_396473 : Nat := 118140960795 + 396473 * 2 ^ 59
def prefixEnd_396473 : Nat := 4983230072969 + 3 ^ 40 * 396473 * 2
def baseEnd_396473 : Nat := 60320360157076305559751

theorem tailTrace_396473 : CollatzResearch.WordTrace tailWord_396473 prefixEnd_396473 60320360157076305559751 := by
  unfold tailWord_396473
  simp only [CollatzResearch.WordTrace]
  refine ⟨14460558292653508042666073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9640372195102338695110715 14460558292653508042666073)
  ·
    refine ⟨10845418719490131031999555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14460558292653508042666073 10845418719490131031999555)
    ·
      refine ⟨16268128079235196547999333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10845418719490131031999555 16268128079235196547999333)
      ·
        refine ⟨3050274014856599352749875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16268128079235196547999333 3050274014856599352749875)
        ·
          refine ⟨4575411022284899029124813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3050274014856599352749875 4575411022284899029124813)
          ·
            refine ⟨1715779133356837135921805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4575411022284899029124813 1715779133356837135921805)
            ·
              refine ⟨643417175008813925970677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1715779133356837135921805 643417175008813925970677)
              ·
                refine ⟨60320360157076305559751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 643417175008813925970677 60320360157076305559751)
                ·
                  rfl

theorem cell20_396473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 5].length) (baseStart_396473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396473 prefixEnd_396473 := by exact prefixLift 396473
  have htrace : WordTrace (prefixWord ++ tailWord_396473) baseStart_396473 baseEnd_396473 := by
    simpa [prefixWord, tailWord_396473, baseEnd_396473] using wordTrace_append hprefix tailTrace_396473
  have hstable : (prefixWord ++ tailWord_396473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396473).length < 2 ^ (prefixWord ++ tailWord_396473).sum := by decide
  have hdescent : baseEnd_396473 < baseStart_396473 := by decide
  rcases family_descends (prefixWord ++ tailWord_396473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396490 : List Nat := [3, 1, 2, 1, 3, 3, 3, 4]
def baseStart_396490 : Nat := 118140960795 + 396490 * 2 ^ 59
def prefixEnd_396490 : Nat := 4983230072969 + 3 ^ 40 * 396490 * 2
def baseEnd_396490 : Nat := 60322946578150804370839

theorem tailTrace_396490 : CollatzResearch.WordTrace tailWord_396490 prefixEnd_396490 60322946578150804370839 := by
  unfold tailWord_396490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3615294583397979986508731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9640785555727946630689949 3615294583397979986508731)
  ·
    refine ⟨5422941875096969979763097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3615294583397979986508731 5422941875096969979763097)
    ·
      refine ⟨4067206406322727484822323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5422941875096969979763097 4067206406322727484822323)
      ·
        refine ⟨6100809609484091227233485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4067206406322727484822323 6100809609484091227233485)
        ·
          refine ⟨2287803603556534210212557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6100809609484091227233485 2287803603556534210212557)
          ·
            refine ⟨857926351333700328829709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2287803603556534210212557 857926351333700328829709)
            ·
              refine ⟨321722381750137623311141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 857926351333700328829709 321722381750137623311141)
              ·
                refine ⟨60322946578150804370839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 321722381750137623311141 60322946578150804370839)
                ·
                  rfl

theorem cell20_396490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_396490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396490 prefixEnd_396490 := by exact prefixLift 396490
  have htrace : WordTrace (prefixWord ++ tailWord_396490) baseStart_396490 baseEnd_396490 := by
    simpa [prefixWord, tailWord_396490, baseEnd_396490] using wordTrace_append hprefix tailTrace_396490
  have hstable : (prefixWord ++ tailWord_396490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396490).length < 2 ^ (prefixWord ++ tailWord_396490).sum := by decide
  have hdescent : baseEnd_396490 < baseStart_396490 := by decide
  rcases family_descends (prefixWord ++ tailWord_396490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396556 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 5]
def baseStart_396556 : Nat := 118140960795 + 396556 * 2 ^ 59
def prefixEnd_396556 : Nat := 4983230072969 + 3 ^ 40 * 396556 * 2
def baseEnd_396556 : Nat := 180998963932849516912247

theorem tailTrace_396556 : CollatzResearch.WordTrace tailWord_396556 prefixEnd_396556 180998963932849516912247 := by
  unfold tailWord_396556
  simp only [CollatzResearch.WordTrace]
  refine ⟨7231792775676406608968761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9642390367568542145291681 7231792775676406608968761)
  ·
    refine ⟨5423844581757304956726571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7231792775676406608968761 5423844581757304956726571)
    ·
      refine ⟨8135766872635957435089857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5423844581757304956726571 8135766872635957435089857)
      ·
        refine ⟨6101825154476968076317393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8135766872635957435089857 6101825154476968076317393)
        ·
          refine ⟨4576368865857726057238045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6101825154476968076317393 4576368865857726057238045)
          ·
            refine ⟨1716138324696647271464267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4576368865857726057238045 1716138324696647271464267)
            ·
              refine ⟨2574207487044970907196401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1716138324696647271464267 2574207487044970907196401)
              ·
                refine ⟨1930655615283728180397301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2574207487044970907196401 1930655615283728180397301)
                ·
                  refine ⟨180998963932849516912247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1930655615283728180397301 180998963932849516912247)
                  ·
                    rfl

theorem cell20_396556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_396556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396556 prefixEnd_396556 := by exact prefixLift 396556
  have htrace : WordTrace (prefixWord ++ tailWord_396556) baseStart_396556 baseEnd_396556 := by
    simpa [prefixWord, tailWord_396556, baseEnd_396556] using wordTrace_append hprefix tailTrace_396556
  have hstable : (prefixWord ++ tailWord_396556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396556).length < 2 ^ (prefixWord ++ tailWord_396556).sum := by decide
  have hdescent : baseEnd_396556 < baseStart_396556 := by decide
  rcases family_descends (prefixWord ++ tailWord_396556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396562 : List Nat := [3, 2, 4, 2, 2, 1, 6]
def baseStart_396562 : Nat := 118140960795 + 396562 * 2 ^ 59
def prefixEnd_396562 : Nat := 4983230072969 + 3 ^ 40 * 396562 * 2
def baseEnd_396562 : Nat := 20111300277371129190247

theorem tailTrace_396562 : CollatzResearch.WordTrace tailWord_396562 prefixEnd_396562 20111300277371129190247 := by
  unfold tailWord_396562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3615951097332769060663985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9642536259554050828437293 3615951097332769060663985)
  ·
    refine ⟨2711963322999576795497989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3615951097332769060663985 2711963322999576795497989)
    ·
      refine ⟨508493123062420649155873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2711963322999576795497989 508493123062420649155873)
      ·
        refine ⟨381369842296815486866905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 508493123062420649155873 381369842296815486866905)
        ·
          refine ⟨286027381722611615150179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381369842296815486866905 286027381722611615150179)
          ·
            refine ⟨429041072583917422725269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286027381722611615150179 429041072583917422725269)
            ·
              refine ⟨20111300277371129190247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 429041072583917422725269 20111300277371129190247)
              ·
                rfl

theorem cell20_396562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 6].length) (baseStart_396562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396562 prefixEnd_396562 := by exact prefixLift 396562
  have htrace : WordTrace (prefixWord ++ tailWord_396562) baseStart_396562 baseEnd_396562 := by
    simpa [prefixWord, tailWord_396562, baseEnd_396562] using wordTrace_append hprefix tailTrace_396562
  have hstable : (prefixWord ++ tailWord_396562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396562).length < 2 ^ (prefixWord ++ tailWord_396562).sum := by decide
  have hdescent : baseEnd_396562 < baseStart_396562 := by decide
  rcases family_descends (prefixWord ++ tailWord_396562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396573 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 5]
def baseStart_396573 : Nat := 118140960795 + 396573 * 2 ^ 59
def prefixEnd_396573 : Nat := 4983230072969 + 3 ^ 40 * 396573 * 2
def baseEnd_396573 : Nat := 181006723196073013345511

theorem tailTrace_396573 : CollatzResearch.WordTrace tailWord_396573 prefixEnd_396573 181006723196073013345511 := by
  unfold tailWord_396573
  simp only [CollatzResearch.WordTrace]
  refine ⟨14464205592291225121306373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9642803728194150080870915 14464205592291225121306373)
  ·
    refine ⟨2712038548554604710244945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14464205592291225121306373 2712038548554604710244945)
    ·
      refine ⟨2034028911415953532683709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2712038548554604710244945 2034028911415953532683709)
      ·
        refine ⟨762760841780982574756391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2034028911415953532683709 762760841780982574756391)
        ·
          refine ⟨1144141262671473862134587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762760841780982574756391 1144141262671473862134587)
          ·
            refine ⟨1716211894007210793201881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144141262671473862134587 1716211894007210793201881)
            ·
              refine ⟨1287158920505408094901411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1716211894007210793201881 1287158920505408094901411)
              ·
                refine ⟨1930738380758112142352117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287158920505408094901411 1930738380758112142352117)
                ·
                  refine ⟨181006723196073013345511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1930738380758112142352117 181006723196073013345511)
                  ·
                    rfl

theorem cell20_396573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_396573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396573 prefixEnd_396573 := by exact prefixLift 396573
  have htrace : WordTrace (prefixWord ++ tailWord_396573) baseStart_396573 baseEnd_396573 := by
    simpa [prefixWord, tailWord_396573, baseEnd_396573] using wordTrace_append hprefix tailTrace_396573
  have hstable : (prefixWord ++ tailWord_396573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396573).length < 2 ^ (prefixWord ++ tailWord_396573).sum := by decide
  have hdescent : baseEnd_396573 < baseStart_396573 := by decide
  rcases family_descends (prefixWord ++ tailWord_396573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396576 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 4]
def baseStart_396576 : Nat := 118140960795 + 396576 * 2 ^ 59
def prefixEnd_396576 : Nat := 4983230072969 + 3 ^ 40 * 396576 * 2
def baseEnd_396576 : Nat := 181008092477818336245499

theorem tailTrace_396576 : CollatzResearch.WordTrace tailWord_396576 prefixEnd_396576 181008092477818336245499 := by
  unfold tailWord_396576
  simp only [CollatzResearch.WordTrace]
  refine ⟨7232157505640178316832791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9642876674186904422443721 7232157505640178316832791)
  ·
    refine ⟨10848236258460267475249187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7232157505640178316832791 10848236258460267475249187)
    ·
      refine ⟨16272354387690401212873781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10848236258460267475249187 16272354387690401212873781)
      ·
        refine ⟨1525533223845975113706917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16272354387690401212873781 1525533223845975113706917)
        ·
          refine ⟨286037479471120333820047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1525533223845975113706917 286037479471120333820047)
          ·
            refine ⟨429056219206680500730071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286037479471120333820047 429056219206680500730071)
            ·
              refine ⟨643584328810020751095107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429056219206680500730071 643584328810020751095107)
              ·
                refine ⟨965376493215031126642661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643584328810020751095107 965376493215031126642661)
                ·
                  refine ⟨181008092477818336245499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965376493215031126642661 181008092477818336245499)
                  ·
                    rfl

theorem cell20_396576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 4].length) (baseStart_396576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396576 prefixEnd_396576 := by exact prefixLift 396576
  have htrace : WordTrace (prefixWord ++ tailWord_396576) baseStart_396576 baseEnd_396576 := by
    simpa [prefixWord, tailWord_396576, baseEnd_396576] using wordTrace_append hprefix tailTrace_396576
  have hstable : (prefixWord ++ tailWord_396576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396576).length < 2 ^ (prefixWord ++ tailWord_396576).sum := by decide
  have hdescent : baseEnd_396576 < baseStart_396576 := by decide
  rcases family_descends (prefixWord ++ tailWord_396576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396608 : List Nat := [2, 1, 1, 2, 2, 1, 3, 8]
def baseStart_396608 : Nat := 118140960795 + 396608 * 2 ^ 59
def prefixEnd_396608 : Nat := 4983230072969 + 3 ^ 40 * 396608 * 2
def baseEnd_396608 : Nat := 60340899383256149059567

theorem tailTrace_396608 : CollatzResearch.WordTrace tailWord_396608 prefixEnd_396608 60340899383256149059567 := by
  unfold tailWord_396608
  simp only [CollatzResearch.WordTrace]
  refine ⟨7232741073582213049415239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9643654764776284065886985 7232741073582213049415239)
  ·
    refine ⟨10849111610373319574122859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7232741073582213049415239 10849111610373319574122859)
    ·
      refine ⟨16273667415559979361184289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10849111610373319574122859 16273667415559979361184289)
      ·
        refine ⟨12205250561669984520888217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16273667415559979361184289 12205250561669984520888217)
        ·
          refine ⟨9153937921252488390666163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12205250561669984520888217 9153937921252488390666163)
          ·
            refine ⟨13730906881878732585999245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9153937921252488390666163 13730906881878732585999245)
            ·
              refine ⟨5149090080704524719749717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13730906881878732585999245 5149090080704524719749717)
              ·
                refine ⟨60340899383256149059567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5149090080704524719749717 60340899383256149059567)
                ·
                  rfl

theorem cell20_396608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_396608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396608 prefixEnd_396608 := by exact prefixLift 396608
  have htrace : WordTrace (prefixWord ++ tailWord_396608) baseStart_396608 baseEnd_396608 := by
    simpa [prefixWord, tailWord_396608, baseEnd_396608] using wordTrace_append hprefix tailTrace_396608
  have hstable : (prefixWord ++ tailWord_396608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396608).length < 2 ^ (prefixWord ++ tailWord_396608).sum := by decide
  have hdescent : baseEnd_396608 < baseStart_396608 := by decide
  rcases family_descends (prefixWord ++ tailWord_396608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396621 : List Nat := [1, 6, 1, 3, 2, 7]
def baseStart_396621 : Nat := 118140960795 + 396621 * 2 ^ 59
def prefixEnd_396621 : Nat := 4983230072969 + 3 ^ 40 * 396621 * 2
def baseEnd_396621 : Nat := 6704764137185117768345

theorem tailTrace_396621 : CollatzResearch.WordTrace tailWord_396621 prefixEnd_396621 6704764137185117768345 := by
  unfold tailWord_396621
  simp only [CollatzResearch.WordTrace]
  refine ⟨14465956296117329319053717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9643970864078219546035811 14465956296117329319053717)
  ·
    refine ⟨678091701380499811830643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14465956296117329319053717 678091701380499811830643)
    ·
      refine ⟨1017137552070749717745965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 678091701380499811830643 1017137552070749717745965)
      ·
        refine ⟨381426582026531144154737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1017137552070749717745965 381426582026531144154737)
        ·
          refine ⟨286069936519898358116053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381426582026531144154737 286069936519898358116053)
          ·
            refine ⟨6704764137185117768345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 286069936519898358116053 6704764137185117768345)
            ·
              rfl

theorem cell20_396621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 7].length) (baseStart_396621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396621 prefixEnd_396621 := by exact prefixLift 396621
  have htrace : WordTrace (prefixWord ++ tailWord_396621) baseStart_396621 baseEnd_396621 := by
    simpa [prefixWord, tailWord_396621, baseEnd_396621] using wordTrace_append hprefix tailTrace_396621
  have hstable : (prefixWord ++ tailWord_396621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396621).length < 2 ^ (prefixWord ++ tailWord_396621).sum := by decide
  have hdescent : baseEnd_396621 < baseStart_396621 := by decide
  rcases family_descends (prefixWord ++ tailWord_396621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396639 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 4]
def baseStart_396639 : Nat := 118140960795 + 396639 * 2 ^ 59
def prefixEnd_396639 : Nat := 4983230072969 + 3 ^ 40 * 396639 * 2
def baseEnd_396639 : Nat := 181036847394470117145241

theorem tailTrace_396639 : CollatzResearch.WordTrace tailWord_396639 prefixEnd_396639 181036847394470117145241 := by
  unfold tailWord_396639
  simp only [CollatzResearch.WordTrace]
  refine ⟨14466612810052118393208971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9644408540034745595472647 14466612810052118393208971)
  ·
    refine ⟨21699919215078177589813457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14466612810052118393208971 21699919215078177589813457)
    ·
      refine ⟨16274939411308633192360093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21699919215078177589813457 16274939411308633192360093)
      ·
        refine ⟨6103102279240737447135035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16274939411308633192360093 6103102279240737447135035)
        ·
          refine ⟨9154653418861106170702553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6103102279240737447135035 9154653418861106170702553)
          ·
            refine ⟨6865990064145829628026915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9154653418861106170702553 6865990064145829628026915)
            ·
              refine ⟨10298985096218744442040373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6865990064145829628026915 10298985096218744442040373)
              ·
                refine ⟨965529852770507291441285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10298985096218744442040373 965529852770507291441285)
                ·
                  refine ⟨181036847394470117145241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965529852770507291441285 181036847394470117145241)
                  ·
                    rfl

theorem cell20_396639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_396639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396639 prefixEnd_396639 := by exact prefixLift 396639
  have htrace : WordTrace (prefixWord ++ tailWord_396639) baseStart_396639 baseEnd_396639 := by
    simpa [prefixWord, tailWord_396639, baseEnd_396639] using wordTrace_append hprefix tailTrace_396639
  have hstable : (prefixWord ++ tailWord_396639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396639).length < 2 ^ (prefixWord ++ tailWord_396639).sum := by decide
  have hdescent : baseEnd_396639 < baseStart_396639 := by decide
  rcases family_descends (prefixWord ++ tailWord_396639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396663 : List Nat := [1, 1, 3, 1, 1, 2, 7, 4]
def baseStart_396663 : Nat := 118140960795 + 396663 * 2 ^ 59
def prefixEnd_396663 : Nat := 4983230072969 + 3 ^ 40 * 396663 * 2
def baseEnd_396663 : Nat := 60349267216144233448381

theorem tailTrace_396663 : CollatzResearch.WordTrace tailWord_396663 prefixEnd_396663 60349267216144233448381 := by
  unfold tailWord_396663
  simp only [CollatzResearch.WordTrace]
  refine ⟨14467488161965170492082643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9644992107976780328055095 14467488161965170492082643)
  ·
    refine ⟨21701232242947755738123965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14467488161965170492082643 21701232242947755738123965)
    ·
      refine ⟨8137962091105408401796487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21701232242947755738123965 8137962091105408401796487)
      ·
        refine ⟨12206943136658112602694731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8137962091105408401796487 12206943136658112602694731)
        ·
          refine ⟨18310414704987168904042097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12206943136658112602694731 18310414704987168904042097)
          ·
            refine ⟨13732811028740376678031573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18310414704987168904042097 13732811028740376678031573)
            ·
              refine ⟨321862758486102578391365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 13732811028740376678031573 321862758486102578391365)
              ·
                refine ⟨60349267216144233448381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 321862758486102578391365 60349267216144233448381)
                ·
                  rfl

theorem cell20_396663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 4].length) (baseStart_396663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396663 prefixEnd_396663 := by exact prefixLift 396663
  have htrace : WordTrace (prefixWord ++ tailWord_396663) baseStart_396663 baseEnd_396663 := by
    simpa [prefixWord, tailWord_396663, baseEnd_396663] using wordTrace_append hprefix tailTrace_396663
  have hstable : (prefixWord ++ tailWord_396663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396663).length < 2 ^ (prefixWord ++ tailWord_396663).sum := by decide
  have hdescent : baseEnd_396663 < baseStart_396663 := by decide
  rcases family_descends (prefixWord ++ tailWord_396663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396684 : List Nat := [2, 2, 1, 2, 1, 3, 9]
def baseStart_396684 : Nat := 118140960795 + 396684 * 2 ^ 59
def prefixEnd_396684 : Nat := 4983230072969 + 3 ^ 40 * 396684 * 2
def baseEnd_396684 : Nat := 20117487402294440071673

theorem tailTrace_396684 : CollatzResearch.WordTrace tailWord_396684 prefixEnd_396684 20117487402294440071673 := by
  unfold tailWord_396684
  simp only [CollatzResearch.WordTrace]
  refine ⟨7234127047444545539298553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9645502729926060719064737 7234127047444545539298553)
  ·
    refine ⟨5425595285583409154473915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7234127047444545539298553 5425595285583409154473915)
    ·
      refine ⟨8138392928375113731710873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5425595285583409154473915 8138392928375113731710873)
      ·
        refine ⟨6103794696281335298783155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8138392928375113731710873 6103794696281335298783155)
        ·
          refine ⟨9155692044422002948174733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6103794696281335298783155 9155692044422002948174733)
          ·
            refine ⟨3433384516658251105565525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9155692044422002948174733 3433384516658251105565525)
            ·
              refine ⟨20117487402294440071673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3433384516658251105565525 20117487402294440071673)
              ·
                rfl

theorem cell20_396684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 9].length) (baseStart_396684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396684 prefixEnd_396684 := by exact prefixLift 396684
  have htrace : WordTrace (prefixWord ++ tailWord_396684) baseStart_396684 baseEnd_396684 := by
    simpa [prefixWord, tailWord_396684, baseEnd_396684] using wordTrace_append hprefix tailTrace_396684
  have hstable : (prefixWord ++ tailWord_396684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396684).length < 2 ^ (prefixWord ++ tailWord_396684).sum := by decide
  have hdescent : baseEnd_396684 < baseStart_396684 := by decide
  rcases family_descends (prefixWord ++ tailWord_396684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396690 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 4]
def baseStart_396690 : Nat := 118140960795 + 396690 * 2 ^ 59
def prefixEnd_396690 : Nat := 4983230072969 + 3 ^ 40 * 396690 * 2
def baseEnd_396690 : Nat := 181060125184140606445033

theorem tailTrace_396690 : CollatzResearch.WordTrace tailWord_396690 prefixEnd_396690 181060125184140606445033 := by
  unfold tailWord_396690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3617118233216838525828881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9645648621911569402210349 3617118233216838525828881)
  ·
    refine ⟨2712838674912628894371661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3617118233216838525828881 2712838674912628894371661)
    ·
      refine ⟨1017314503092235835389373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2712838674912628894371661 1017314503092235835389373)
      ·
        refine ⟨381492938659588438271015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1017314503092235835389373 381492938659588438271015)
        ·
          refine ⟨572239407989382657406523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381492938659588438271015 572239407989382657406523)
          ·
            refine ⟨858359111984073986109785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572239407989382657406523 858359111984073986109785)
            ·
              refine ⟨643769333988055489582339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858359111984073986109785 643769333988055489582339)
              ·
                refine ⟨965654000982083234373509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643769333988055489582339 965654000982083234373509)
                ·
                  refine ⟨181060125184140606445033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965654000982083234373509 181060125184140606445033)
                  ·
                    rfl

theorem cell20_396690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_396690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396690 prefixEnd_396690 := by exact prefixLift 396690
  have htrace : WordTrace (prefixWord ++ tailWord_396690) baseStart_396690 baseEnd_396690 := by
    simpa [prefixWord, tailWord_396690, baseEnd_396690] using wordTrace_append hprefix tailTrace_396690
  have hstable : (prefixWord ++ tailWord_396690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396690).length < 2 ^ (prefixWord ++ tailWord_396690).sum := by decide
  have hdescent : baseEnd_396690 < baseStart_396690 := by decide
  rcases family_descends (prefixWord ++ tailWord_396690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396746 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_396746 : Nat := 118140960795 + 396746 * 2 ^ 59
def prefixEnd_396746 : Nat := 4983230072969 + 3 ^ 40 * 396746 * 2
def baseEnd_396746 : Nat := 181085685110053300578137

theorem tailTrace_396746 : CollatzResearch.WordTrace tailWord_396746 prefixEnd_396746 181085685110053300578137 := by
  unfold tailWord_396746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3617628855166118916838523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9647010280442983778236061 3617628855166118916838523)
  ·
    refine ⟨5426443282749178375257785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3617628855166118916838523 5426443282749178375257785)
    ·
      refine ⟨4069832462061883781443339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5426443282749178375257785 4069832462061883781443339)
      ·
        refine ⟨6104748693092825672165009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4069832462061883781443339 6104748693092825672165009)
        ·
          refine ⟨4578561519819619254123757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6104748693092825672165009 4578561519819619254123757)
          ·
            refine ⟨1716960569932357220296409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4578561519819619254123757 1716960569932357220296409)
            ·
              refine ⟨1287720427449267915222307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1716960569932357220296409 1287720427449267915222307)
              ·
                refine ⟨1931580641173901872833461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287720427449267915222307 1931580641173901872833461)
                ·
                  refine ⟨181085685110053300578137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1931580641173901872833461 181085685110053300578137)
                  ·
                    rfl

theorem cell20_396746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_396746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396746 prefixEnd_396746 := by exact prefixLift 396746
  have htrace : WordTrace (prefixWord ++ tailWord_396746) baseStart_396746 baseEnd_396746 := by
    simpa [prefixWord, tailWord_396746, baseEnd_396746] using wordTrace_append hprefix tailTrace_396746
  have hstable : (prefixWord ++ tailWord_396746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396746).length < 2 ^ (prefixWord ++ tailWord_396746).sum := by decide
  have hdescent : baseEnd_396746 < baseStart_396746 := by decide
  rcases family_descends (prefixWord ++ tailWord_396746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396756 : List Nat := [2, 4, 1, 2, 3, 1, 2, 5]
def baseStart_396756 : Nat := 118140960795 + 396756 * 2 ^ 59
def prefixEnd_396756 : Nat := 4983230072969 + 3 ^ 40 * 396756 * 2
def baseEnd_396756 : Nat := 60363416460845903414921

theorem tailTrace_396756 : CollatzResearch.WordTrace tailWord_396756 prefixEnd_396756 60363416460845903414921 := by
  unfold tailWord_396756
  simp only [CollatzResearch.WordTrace]
  refine ⟨7235440075314123687609061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9647253433752164916812081 7235440075314123687609061)
  ·
    refine ⟨1356645014121398191426699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7235440075314123687609061 1356645014121398191426699)
    ·
      refine ⟨2034967521182097287140049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1356645014121398191426699 2034967521182097287140049)
      ·
        refine ⟨1526225640886572965355037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2034967521182097287140049 1526225640886572965355037)
        ·
          refine ⟨572334615332464862008139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1526225640886572965355037 572334615332464862008139)
          ·
            refine ⟨858501922998697293012209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572334615332464862008139 858501922998697293012209)
            ·
              refine ⟨643876442249022969759157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858501922998697293012209 643876442249022969759157)
              ·
                refine ⟨60363416460845903414921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 643876442249022969759157 60363416460845903414921)
                ·
                  rfl

theorem cell20_396756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_396756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396756 prefixEnd_396756 := by exact prefixLift 396756
  have htrace : WordTrace (prefixWord ++ tailWord_396756) baseStart_396756 baseEnd_396756 := by
    simpa [prefixWord, tailWord_396756, baseEnd_396756] using wordTrace_append hprefix tailTrace_396756
  have hstable : (prefixWord ++ tailWord_396756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396756).length < 2 ^ (prefixWord ++ tailWord_396756).sum := by decide
  have hdescent : baseEnd_396756 < baseStart_396756 := by decide
  rcases family_descends (prefixWord ++ tailWord_396756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396760 : List Nat := [2, 1, 2, 2, 2, 1, 3, 7]
def baseStart_396760 : Nat := 118140960795 + 396760 * 2 ^ 59
def prefixEnd_396760 : Nat := 4983230072969 + 3 ^ 40 * 396760 * 2
def baseEnd_396760 : Nat := 60364025030510491370471

theorem tailTrace_396760 : CollatzResearch.WordTrace tailWord_396760 prefixEnd_396760 60364025030510491370471 := by
  unfold tailWord_396760
  simp only [CollatzResearch.WordTrace]
  refine ⟨7235513021306878029181867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9647350695075837372242489 7235513021306878029181867)
  ·
    refine ⟨10853269531960317043772801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7235513021306878029181867 10853269531960317043772801)
    ·
      refine ⟨8139952148970237782829601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10853269531960317043772801 8139952148970237782829601)
      ·
        refine ⟨6104964111727678337122201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8139952148970237782829601 6104964111727678337122201)
        ·
          refine ⟨4578723083795758752841651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6104964111727678337122201 4578723083795758752841651)
          ·
            refine ⟨6868084625693638129262477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4578723083795758752841651 6868084625693638129262477)
            ·
              refine ⟨2575531734635114298473429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6868084625693638129262477 2575531734635114298473429)
              ·
                refine ⟨60364025030510491370471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2575531734635114298473429 60364025030510491370471)
                ·
                  rfl

theorem cell20_396760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_396760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396760 prefixEnd_396760 := by exact prefixLift 396760
  have htrace : WordTrace (prefixWord ++ tailWord_396760) baseStart_396760 baseEnd_396760 := by
    simpa [prefixWord, tailWord_396760, baseEnd_396760] using wordTrace_append hprefix tailTrace_396760
  have hstable : (prefixWord ++ tailWord_396760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396760).length < 2 ^ (prefixWord ++ tailWord_396760).sum := by decide
  have hdescent : baseEnd_396760 < baseStart_396760 := by decide
  rcases family_descends (prefixWord ++ tailWord_396760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396804 : List Nat := [2, 3, 2, 3, 2, 1, 1, 4, 2]
def baseStart_396804 : Nat := 118140960795 + 396804 * 2 ^ 59
def prefixEnd_396804 : Nat := 4983230072969 + 3 ^ 40 * 396804 * 2
def baseEnd_396804 : Nat := 181112157890462876644567

theorem tailTrace_396804 : CollatzResearch.WordTrace tailWord_396804 prefixEnd_396804 181112157890462876644567 := by
  unfold tailWord_396804
  simp only [CollatzResearch.WordTrace]
  refine ⟨7236315427227175786482733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9648420569636234381976977 7236315427227175786482733)
  ·
    refine ⟨2713618285210190919931025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7236315427227175786482733 2713618285210190919931025)
    ·
      refine ⟨2035213713907643189948269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2713618285210190919931025 2035213713907643189948269)
      ·
        refine ⟨763205142715366196230601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2035213713907643189948269 763205142715366196230601)
        ·
          refine ⟨572403857036524647172951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 763205142715366196230601 572403857036524647172951)
          ·
            refine ⟨858605785554786970759427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572403857036524647172951 858605785554786970759427)
            ·
              refine ⟨1287908678332180456139141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858605785554786970759427 1287908678332180456139141)
              ·
                refine ⟨241482877187283835526089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1287908678332180456139141 241482877187283835526089)
                ·
                  refine ⟨181112157890462876644567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241482877187283835526089 181112157890462876644567)
                  ·
                    rfl

theorem cell20_396804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_396804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396804 prefixEnd_396804 := by exact prefixLift 396804
  have htrace : WordTrace (prefixWord ++ tailWord_396804) baseStart_396804 baseEnd_396804 := by
    simpa [prefixWord, tailWord_396804, baseEnd_396804] using wordTrace_append hprefix tailTrace_396804
  have hstable : (prefixWord ++ tailWord_396804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396804).length < 2 ^ (prefixWord ++ tailWord_396804).sum := by decide
  have hdescent : baseEnd_396804 < baseStart_396804 := by decide
  rcases family_descends (prefixWord ++ tailWord_396804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396832 : List Nat := [2, 1, 1, 6, 1, 2, 3, 4]
def baseStart_396832 : Nat := 118140960795 + 396832 * 2 ^ 59
def prefixEnd_396832 : Nat := 4983230072969 + 3 ^ 40 * 396832 * 2
def baseEnd_396832 : Nat := 60374979284473074570373

theorem tailTrace_396832 : CollatzResearch.WordTrace tailWord_396832 prefixEnd_396832 60374979284473074570373 := by
  unfold tailWord_396832
  simp only [CollatzResearch.WordTrace]
  refine ⟨7236826049176456177492375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9649101398901941569989833 7236826049176456177492375)
  ·
    refine ⟨10855239073764684266238563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7236826049176456177492375 10855239073764684266238563)
    ·
      refine ⟨16282858610647026399357845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10855239073764684266238563 16282858610647026399357845)
      ·
        refine ⟨763258997374079362469899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16282858610647026399357845 763258997374079362469899)
        ·
          refine ⟨1144888496061119043704849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763258997374079362469899 1144888496061119043704849)
          ·
            refine ⟨858666372045839282778637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1144888496061119043704849 858666372045839282778637)
            ·
              refine ⟨321999889517189731041989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 858666372045839282778637 321999889517189731041989)
              ·
                refine ⟨60374979284473074570373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 321999889517189731041989 60374979284473074570373)
                ·
                  rfl

theorem cell20_396832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_396832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396832 prefixEnd_396832 := by exact prefixLift 396832
  have htrace : WordTrace (prefixWord ++ tailWord_396832) baseStart_396832 baseEnd_396832 := by
    simpa [prefixWord, tailWord_396832, baseEnd_396832] using wordTrace_append hprefix tailTrace_396832
  have hstable : (prefixWord ++ tailWord_396832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396832).length < 2 ^ (prefixWord ++ tailWord_396832).sum := by decide
  have hdescent : baseEnd_396832 < baseStart_396832 := by decide
  rcases family_descends (prefixWord ++ tailWord_396832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396874 : List Nat := [3, 1, 2, 1, 1, 3, 2, 7]
def baseStart_396874 : Nat := 118140960795 + 396874 * 2 ^ 59
def prefixEnd_396874 : Nat := 4983230072969 + 3 ^ 40 * 396874 * 2
def baseEnd_396874 : Nat := 60381369265951248103649

theorem tailTrace_396874 : CollatzResearch.WordTrace tailWord_396874 prefixEnd_396874 60381369265951248103649 := by
  unfold tailWord_396874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3618795991050188382003419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9650122642800502352009117 3618795991050188382003419)
  ·
    refine ⟨5428193986575282573005129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3618795991050188382003419 5428193986575282573005129)
    ·
      refine ⟨4071145489931461929753847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5428193986575282573005129 4071145489931461929753847)
      ·
        refine ⟨6106718234897192894630771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4071145489931461929753847 6106718234897192894630771)
        ·
          refine ⟨9160077352345789341946157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6106718234897192894630771 9160077352345789341946157)
          ·
            refine ⟨3435029007129671003229809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9160077352345789341946157 3435029007129671003229809)
            ·
              refine ⟨2576271755347253252422357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3435029007129671003229809 2576271755347253252422357)
              ·
                refine ⟨60381369265951248103649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2576271755347253252422357 60381369265951248103649)
                ·
                  rfl

theorem cell20_396874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_396874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396874 prefixEnd_396874 := by exact prefixLift 396874
  have htrace : WordTrace (prefixWord ++ tailWord_396874) baseStart_396874 baseEnd_396874 := by
    simpa [prefixWord, tailWord_396874, baseEnd_396874] using wordTrace_append hprefix tailTrace_396874
  have hstable : (prefixWord ++ tailWord_396874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396874).length < 2 ^ (prefixWord ++ tailWord_396874).sum := by decide
  have hdescent : baseEnd_396874 < baseStart_396874 := by decide
  rcases family_descends (prefixWord ++ tailWord_396874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396901 : List Nat := [1, 3, 1, 3, 3, 1, 3, 3, 2]
def baseStart_396901 : Nat := 118140960795 + 396901 * 2 ^ 59
def prefixEnd_396901 : Nat := 4983230072969 + 3 ^ 40 * 396901 * 2
def baseEnd_396901 : Nat := 181156431333561650410837

theorem tailTrace_396901 : CollatzResearch.WordTrace tailWord_396901 prefixEnd_396901 181156431333561650410837 := by
  unfold tailWord_396901
  simp only [CollatzResearch.WordTrace]
  refine ⟨14476168735102937139246557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9650779156735291426164371 14476168735102937139246557)
  ·
    refine ⟨5428563275663601427217459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14476168735102937139246557 5428563275663601427217459)
    ·
      refine ⟨8142844913495402140826189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5428563275663601427217459 8142844913495402140826189)
      ·
        refine ⟨3053566842560775802809821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8142844913495402140826189 3053566842560775802809821)
        ·
          refine ⟨1145087565960290926053683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3053566842560775802809821 1145087565960290926053683)
          ·
            refine ⟨1717631348940436389080525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145087565960290926053683 1717631348940436389080525)
            ·
              refine ⟨644111755852663645905197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1717631348940436389080525 644111755852663645905197)
              ·
                refine ⟨241541908444748867214449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 644111755852663645905197 241541908444748867214449)
                ·
                  refine ⟨181156431333561650410837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241541908444748867214449 181156431333561650410837)
                  ·
                    rfl

theorem cell20_396901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_396901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396901 prefixEnd_396901 := by exact prefixLift 396901
  have htrace : WordTrace (prefixWord ++ tailWord_396901) baseStart_396901 baseEnd_396901 := by
    simpa [prefixWord, tailWord_396901, baseEnd_396901] using wordTrace_append hprefix tailTrace_396901
  have hstable : (prefixWord ++ tailWord_396901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396901).length < 2 ^ (prefixWord ++ tailWord_396901).sum := by decide
  have hdescent : baseEnd_396901 < baseStart_396901 := by decide
  rcases family_descends (prefixWord ++ tailWord_396901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396912 : List Nat := [2, 1, 1, 1, 6, 1, 8]
def baseStart_396912 : Nat := 118140960795 + 396912 * 2 ^ 59
def prefixEnd_396912 : Nat := 4983230072969 + 3 ^ 40 * 396912 * 2
def baseEnd_396912 : Nat := 20129050225921611227125

theorem tailTrace_396912 : CollatzResearch.WordTrace tailWord_396912 prefixEnd_396912 20129050225921611227125 := by
  unfold tailWord_396912
  simp only [CollatzResearch.WordTrace]
  refine ⟨7238284969031543008948495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9651046625375390678597993 7238284969031543008948495)
  ·
    refine ⟨10857427453547314513422743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7238284969031543008948495 10857427453547314513422743)
    ·
      refine ⟨16286141180320971770134115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10857427453547314513422743 16286141180320971770134115)
      ·
        refine ⟨24429211770481457655201173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16286141180320971770134115 24429211770481457655201173)
        ·
          refine ⟨1145119301741318327587555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24429211770481457655201173 1145119301741318327587555)
          ·
            refine ⟨1717678952611977491381333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145119301741318327587555 1717678952611977491381333)
            ·
              refine ⟨20129050225921611227125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1717678952611977491381333 20129050225921611227125)
              ·
                rfl

theorem cell20_396912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 8].length) (baseStart_396912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396912 prefixEnd_396912 := by exact prefixLift 396912
  have htrace : WordTrace (prefixWord ++ tailWord_396912) baseStart_396912 baseEnd_396912 := by
    simpa [prefixWord, tailWord_396912, baseEnd_396912] using wordTrace_append hprefix tailTrace_396912
  have hstable : (prefixWord ++ tailWord_396912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396912).length < 2 ^ (prefixWord ++ tailWord_396912).sum := by decide
  have hdescent : baseEnd_396912 < baseStart_396912 := by decide
  rcases family_descends (prefixWord ++ tailWord_396912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396929 : List Nat := [1, 2, 4, 2, 1, 3, 2, 5]
def baseStart_396929 : Nat := 118140960795 + 396929 * 2 ^ 59
def prefixEnd_396929 : Nat := 4983230072969 + 3 ^ 40 * 396929 * 2
def baseEnd_396929 : Nat := 60389737098839332492463

theorem tailTrace_396929 : CollatzResearch.WordTrace tailWord_396929 prefixEnd_396929 60389737098839332492463 := by
  unfold tailWord_396929
  simp only [CollatzResearch.WordTrace]
  refine ⟨14477189979001497921265841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9651459986000998614177227 14477189979001497921265841)
  ·
    refine ⟨10857892484251123440949381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14477189979001497921265841 10857892484251123440949381)
    ·
      refine ⟨2035854840797085645178009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10857892484251123440949381 2035854840797085645178009)
      ·
        refine ⟨1526891130597814233883507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2035854840797085645178009 1526891130597814233883507)
        ·
          refine ⟨2290336695896721350825261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1526891130597814233883507 2290336695896721350825261)
          ·
            refine ⟨858876260961270506559473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2290336695896721350825261 858876260961270506559473)
            ·
              refine ⟨644157195720952879919605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858876260961270506559473 644157195720952879919605)
              ·
                refine ⟨60389737098839332492463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 644157195720952879919605 60389737098839332492463)
                ·
                  rfl

theorem cell20_396929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 5].length) (baseStart_396929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396929 prefixEnd_396929 := by exact prefixLift 396929
  have htrace : WordTrace (prefixWord ++ tailWord_396929) baseStart_396929 baseEnd_396929 := by
    simpa [prefixWord, tailWord_396929, baseEnd_396929] using wordTrace_append hprefix tailTrace_396929
  have hstable : (prefixWord ++ tailWord_396929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396929).length < 2 ^ (prefixWord ++ tailWord_396929).sum := by decide
  have hdescent : baseEnd_396929 < baseStart_396929 := by decide
  rcases family_descends (prefixWord ++ tailWord_396929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397036 : List Nat := [2, 2, 1, 1, 2, 2, 4, 4, 2]
def baseStart_397036 : Nat := 118140960795 + 397036 * 2 ^ 59
def prefixEnd_397036 : Nat := 4983230072969 + 3 ^ 40 * 397036 * 2
def baseEnd_397036 : Nat := 181218049012101180910285

theorem tailTrace_397036 : CollatzResearch.WordTrace tailWord_397036 prefixEnd_397036 181218049012101180910285 := by
  unfold tailWord_397036
  simp only [CollatzResearch.WordTrace]
  refine ⟨7240546294806927597705481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9654061726409236796940641 7240546294806927597705481)
  ·
    refine ⟨5430409721105195698279111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7240546294806927597705481 5430409721105195698279111)
    ·
      refine ⟨8145614581657793547418667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5430409721105195698279111 8145614581657793547418667)
      ·
        refine ⟨12218421872486690321128001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8145614581657793547418667 12218421872486690321128001)
        ·
          refine ⟨9163816404365017740846001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12218421872486690321128001 9163816404365017740846001)
          ·
            refine ⟨6872862303273763305634501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9163816404365017740846001 6872862303273763305634501)
            ·
              refine ⟨1288661681863830619806469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6872862303273763305634501 1288661681863830619806469)
              ·
                refine ⟨241624065349468241213713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1288661681863830619806469 241624065349468241213713)
                ·
                  refine ⟨181218049012101180910285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241624065349468241213713 181218049012101180910285)
                  ·
                    rfl

theorem cell20_397036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_397036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397036 prefixEnd_397036 := by exact prefixLift 397036
  have htrace : WordTrace (prefixWord ++ tailWord_397036) baseStart_397036 baseEnd_397036 := by
    simpa [prefixWord, tailWord_397036, baseEnd_397036] using wordTrace_append hprefix tailTrace_397036
  have hstable : (prefixWord ++ tailWord_397036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397036).length < 2 ^ (prefixWord ++ tailWord_397036).sum := by decide
  have hdescent : baseEnd_397036 < baseStart_397036 := by decide
  rcases family_descends (prefixWord ++ tailWord_397036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397046 : List Nat := [5, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_397046 : Nat := 118140960795 + 397046 * 2 ^ 59
def prefixEnd_397046 : Nat := 4983230072969 + 3 ^ 40 * 397046 * 2
def baseEnd_397046 : Nat := 181222613284585590576911

theorem tailTrace_397046 : CollatzResearch.WordTrace tailWord_397046 prefixEnd_397046 181222613284585590576911 := by
  unfold tailWord_397046
  simp only [CollatzResearch.WordTrace]
  refine ⟨905091082473601681454687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9654304879718417935516661 905091082473601681454687)
  ·
    refine ⟨1357636623710402522182031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 905091082473601681454687 1357636623710402522182031)
    ·
      refine ⟨2036454935565603783273047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1357636623710402522182031 2036454935565603783273047)
      ·
        refine ⟨3054682403348405674909571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2036454935565603783273047 3054682403348405674909571)
        ·
          refine ⟨4582023605022608512364357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3054682403348405674909571 4582023605022608512364357)
          ·
            refine ⟨859129425941739096068317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4582023605022608512364357 859129425941739096068317)
            ·
              refine ⟨322173534728152161025619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 859129425941739096068317 322173534728152161025619)
              ·
                refine ⟨483260302092228241538429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322173534728152161025619 483260302092228241538429)
                ·
                  refine ⟨181222613284585590576911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483260302092228241538429 181222613284585590576911)
                  ·
                    rfl

theorem cell20_397046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_397046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397046 prefixEnd_397046 := by exact prefixLift 397046
  have htrace : WordTrace (prefixWord ++ tailWord_397046) baseStart_397046 baseEnd_397046 := by
    simpa [prefixWord, tailWord_397046, baseEnd_397046] using wordTrace_append hprefix tailTrace_397046
  have hstable : (prefixWord ++ tailWord_397046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397046).length < 2 ^ (prefixWord ++ tailWord_397046).sum := by decide
  have hdescent : baseEnd_397046 < baseStart_397046 := by decide
  rcases family_descends (prefixWord ++ tailWord_397046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397057 : List Nat := [1, 2, 4, 1, 1, 1, 4, 2, 4]
def baseStart_397057 : Nat := 118140960795 + 397057 * 2 ^ 59
def prefixEnd_397057 : Nat := 4983230072969 + 3 ^ 40 * 397057 * 2
def baseEnd_397057 : Nat := 181227633984318441210199

theorem tailTrace_397057 : CollatzResearch.WordTrace tailWord_397057 prefixEnd_397057 181227633984318441210199 := by
  unfold tailWord_397057
  simp only [CollatzResearch.WordTrace]
  refine ⟨14481858522537775781925425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9654572348358517187950283 14481858522537775781925425)
  ·
    refine ⟨10861393891903331836444069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14481858522537775781925425 10861393891903331836444069)
    ·
      refine ⟨2036511354731874719333263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10861393891903331836444069 2036511354731874719333263)
      ·
        refine ⟨3054767032097812078999895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2036511354731874719333263 3054767032097812078999895)
        ·
          refine ⟨4582150548146718118499843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3054767032097812078999895 4582150548146718118499843)
          ·
            refine ⟨6873225822220077177749765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4582150548146718118499843 6873225822220077177749765)
            ·
              refine ⟨1288729841666264470828081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6873225822220077177749765 1288729841666264470828081)
              ·
                refine ⟨966547381249698353121061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1288729841666264470828081 966547381249698353121061)
                ·
                  refine ⟨181227633984318441210199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 966547381249698353121061 181227633984318441210199)
                  ·
                    rfl

theorem cell20_397057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_397057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397057 prefixEnd_397057 := by exact prefixLift 397057
  have htrace : WordTrace (prefixWord ++ tailWord_397057) baseStart_397057 baseEnd_397057 := by
    simpa [prefixWord, tailWord_397057, baseEnd_397057] using wordTrace_append hprefix tailTrace_397057
  have hstable : (prefixWord ++ tailWord_397057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397057).length < 2 ^ (prefixWord ++ tailWord_397057).sum := by decide
  have hdescent : baseEnd_397057 < baseStart_397057 := by decide
  rcases family_descends (prefixWord ++ tailWord_397057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397060 : List Nat := [2, 3, 2, 2, 1, 4, 2, 4]
def baseStart_397060 : Nat := 118140960795 + 397060 * 2 ^ 59
def prefixEnd_397060 : Nat := 4983230072969 + 3 ^ 40 * 397060 * 2
def baseEnd_397060 : Nat := 60409667755354588036729

theorem tailTrace_397060 : CollatzResearch.WordTrace tailWord_397060 prefixEnd_397060 60409667755354588036729 := by
  unfold tailWord_397060
  simp only [CollatzResearch.WordTrace]
  refine ⟨7240983970763453647142317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9654645294351271529523089 7240983970763453647142317)
  ·
    refine ⟨2715368989036295117678369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7240983970763453647142317 2715368989036295117678369)
    ·
      refine ⟨2036526741777221338258777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2715368989036295117678369 2036526741777221338258777)
      ·
        refine ⟨1527395056332916003694083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2036526741777221338258777 1527395056332916003694083)
        ·
          refine ⟨2291092584499374005541125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1527395056332916003694083 2291092584499374005541125)
          ·
            refine ⟨429579859593632626038961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2291092584499374005541125 429579859593632626038961)
            ·
              refine ⟨322184894695224469529221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429579859593632626038961 322184894695224469529221)
              ·
                refine ⟨60409667755354588036729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322184894695224469529221 60409667755354588036729)
                ·
                  rfl

theorem cell20_397060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_397060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397060 prefixEnd_397060 := by exact prefixLift 397060
  have htrace : WordTrace (prefixWord ++ tailWord_397060) baseStart_397060 baseEnd_397060 := by
    simpa [prefixWord, tailWord_397060, baseEnd_397060] using wordTrace_append hprefix tailTrace_397060
  have hstable : (prefixWord ++ tailWord_397060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397060).length < 2 ^ (prefixWord ++ tailWord_397060).sum := by decide
  have hdescent : baseEnd_397060 < baseStart_397060 := by decide
  rcases family_descends (prefixWord ++ tailWord_397060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397062 : List Nat := [6, 2, 2, 1, 1, 2, 1, 3, 2]
def baseStart_397062 : Nat := 118140960795 + 397062 * 2 ^ 59
def prefixEnd_397062 : Nat := 4983230072969 + 3 ^ 40 * 397062 * 2
def baseEnd_397062 : Nat := 181229916120560646043513

theorem tailTrace_397062 : CollatzResearch.WordTrace tailWord_397062 prefixEnd_397062 181229916120560646043513 := by
  unfold tailWord_397062
  simp only [CollatzResearch.WordTrace]
  refine ⟨452563777734989426120545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9654693925013107757238293 452563777734989426120545)
  ·
    refine ⟨339422833301242069590409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 452563777734989426120545 339422833301242069590409)
    ·
      refine ⟨254567124975931552192807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339422833301242069590409 254567124975931552192807)
      ·
        refine ⟨381850687463897328289211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254567124975931552192807 381850687463897328289211)
        ·
          refine ⟨572776031195845992433817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381850687463897328289211 572776031195845992433817)
          ·
            refine ⟨429582023396884494325363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572776031195845992433817 429582023396884494325363)
            ·
              refine ⟨644373035095326741488045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429582023396884494325363 644373035095326741488045)
              ·
                refine ⟨241639888160747528058017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 644373035095326741488045 241639888160747528058017)
                ·
                  refine ⟨181229916120560646043513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241639888160747528058017 181229916120560646043513)
                  ·
                    rfl

theorem cell20_397062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_397062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397062 prefixEnd_397062 := by exact prefixLift 397062
  have htrace : WordTrace (prefixWord ++ tailWord_397062) baseStart_397062 baseEnd_397062 := by
    simpa [prefixWord, tailWord_397062, baseEnd_397062] using wordTrace_append hprefix tailTrace_397062
  have hstable : (prefixWord ++ tailWord_397062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397062).length < 2 ^ (prefixWord ++ tailWord_397062).sum := by decide
  have hdescent : baseEnd_397062 < baseStart_397062 := by decide
  rcases family_descends (prefixWord ++ tailWord_397062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397064 : List Nat := [2, 1, 3, 2, 2, 1, 3, 6]
def baseStart_397064 : Nat := 118140960795 + 397064 * 2 ^ 59
def prefixEnd_397064 : Nat := 4983230072969 + 3 ^ 40 * 397064 * 2
def baseEnd_397064 : Nat := 60410276325019175992279

theorem tailTrace_397064 : CollatzResearch.WordTrace tailWord_397064 prefixEnd_397064 60410276325019175992279 := by
  unfold tailWord_397064
  simp only [CollatzResearch.WordTrace]
  refine ⟨7241056916756207988715123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9654742555674943984953497 7241056916756207988715123)
  ·
    refine ⟨10861585375134311983072685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7241056916756207988715123 10861585375134311983072685)
    ·
      refine ⟨4073094515675366993652257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10861585375134311983072685 4073094515675366993652257)
      ·
        refine ⟨3054820886756525245239193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4073094515675366993652257 3054820886756525245239193)
        ·
          refine ⟨2291115665067393933929395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3054820886756525245239193 2291115665067393933929395)
          ·
            refine ⟨3436673497601090900894093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291115665067393933929395 3436673497601090900894093)
            ·
              refine ⟨1288752561600409087835285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3436673497601090900894093 1288752561600409087835285)
              ·
                refine ⟨60410276325019175992279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1288752561600409087835285 60410276325019175992279)
                ·
                  rfl

theorem cell20_397064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_397064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397064 prefixEnd_397064 := by exact prefixLift 397064
  have htrace : WordTrace (prefixWord ++ tailWord_397064) baseStart_397064 baseEnd_397064 := by
    simpa [prefixWord, tailWord_397064, baseEnd_397064] using wordTrace_append hprefix tailTrace_397064
  have hstable : (prefixWord ++ tailWord_397064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397064).length < 2 ^ (prefixWord ++ tailWord_397064).sum := by decide
  have hdescent : baseEnd_397064 < baseStart_397064 := by decide
  rcases family_descends (prefixWord ++ tailWord_397064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397088 : List Nat := [2, 1, 1, 5, 1, 1, 2, 4, 3]
def baseStart_397088 : Nat := 118140960795 + 397088 * 2 ^ 59
def prefixEnd_397088 : Nat := 4983230072969 + 3 ^ 40 * 397088 * 2
def baseEnd_397088 : Nat := 181241783229020111176739

theorem tailTrace_397088 : CollatzResearch.WordTrace tailWord_397088 prefixEnd_397088 181241783229020111176739 := by
  unfold tailWord_397088
  simp only [CollatzResearch.WordTrace]
  refine ⟨7241494592712734038151959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9655326123616978717535945 7241494592712734038151959)
  ·
    refine ⟨10862241889069101057227939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7241494592712734038151959 10862241889069101057227939)
    ·
      refine ⟨16293362833603651585841909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10862241889069101057227939 16293362833603651585841909)
      ·
        refine ⟨1527502765650342336172679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16293362833603651585841909 1527502765650342336172679)
        ·
          refine ⟨2291254148475513504259019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1527502765650342336172679 2291254148475513504259019)
          ·
            refine ⟨3436881222713270256388529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291254148475513504259019 3436881222713270256388529)
            ·
              refine ⟨2577660917034952692291397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3436881222713270256388529 2577660917034952692291397)
              ·
                refine ⟨483311421944053629804637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2577660917034952692291397 483311421944053629804637)
                ·
                  refine ⟨181241783229020111176739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483311421944053629804637 181241783229020111176739)
                  ·
                    rfl

theorem cell20_397088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_397088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397088 prefixEnd_397088 := by exact prefixLift 397088
  have htrace : WordTrace (prefixWord ++ tailWord_397088) baseStart_397088 baseEnd_397088 := by
    simpa [prefixWord, tailWord_397088, baseEnd_397088] using wordTrace_append hprefix tailTrace_397088
  have hstable : (prefixWord ++ tailWord_397088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397088).length < 2 ^ (prefixWord ++ tailWord_397088).sum := by decide
  have hdescent : baseEnd_397088 < baseStart_397088 := by decide
  rcases family_descends (prefixWord ++ tailWord_397088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397105 : List Nat := [1, 2, 2, 3, 2, 2, 4, 1, 3]
def baseStart_397105 : Nat := 118140960795 + 397105 * 2 ^ 59
def prefixEnd_397105 : Nat := 4983230072969 + 3 ^ 40 * 397105 * 2
def baseEnd_397105 : Nat := 181249542492243607610003

theorem tailTrace_397105 : CollatzResearch.WordTrace tailWord_397105 prefixEnd_397105 181249542492243607610003 := by
  unfold tailWord_397105
  simp only [CollatzResearch.WordTrace]
  refine ⟨14483609226363879979672769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9655739484242586653115179 14483609226363879979672769)
  ·
    refine ⟨10862706919772909984754577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14483609226363879979672769 10862706919772909984754577)
    ·
      refine ⟨8147030189829682488565933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10862706919772909984754577 8147030189829682488565933)
      ·
        refine ⟨3055136321186130933212225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8147030189829682488565933 3055136321186130933212225)
        ·
          refine ⟨2291352240889598199909169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3055136321186130933212225 2291352240889598199909169)
          ·
            refine ⟨1718514180667198649931877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2291352240889598199909169 1718514180667198649931877)
            ·
              refine ⟨322221408875099746862227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1718514180667198649931877 322221408875099746862227)
              ·
                refine ⟨483332113312649620293341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322221408875099746862227 483332113312649620293341)
                ·
                  refine ⟨181249542492243607610003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483332113312649620293341 181249542492243607610003)
                  ·
                    rfl

theorem cell20_397105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_397105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397105 prefixEnd_397105 := by exact prefixLift 397105
  have htrace : WordTrace (prefixWord ++ tailWord_397105) baseStart_397105 baseEnd_397105 := by
    simpa [prefixWord, tailWord_397105, baseEnd_397105] using wordTrace_append hprefix tailTrace_397105
  have hstable : (prefixWord ++ tailWord_397105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397105).length < 2 ^ (prefixWord ++ tailWord_397105).sum := by decide
  have hdescent : baseEnd_397105 < baseStart_397105 := by decide
  rcases family_descends (prefixWord ++ tailWord_397105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397140 : List Nat := [2, 4, 1, 1, 3, 9]
def baseStart_397140 : Nat := 118140960795 + 397140 * 2 ^ 59
def prefixEnd_397140 : Nat := 4983230072969 + 3 ^ 40 * 397140 * 2
def baseEnd_397140 : Nat := 6713537683182927460859

theorem tailTrace_397140 : CollatzResearch.WordTrace tailWord_397140 prefixEnd_397140 6713537683182927460859 := by
  unfold tailWord_397140
  simp only [CollatzResearch.WordTrace]
  refine ⟨7242442890618540478598437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9656590520824720638131249 7242442890618540478598437)
  ·
    refine ⟨1357958041990976339737207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7242442890618540478598437 1357958041990976339737207)
    ·
      refine ⟨2036937062986464509605811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1357958041990976339737207 2036937062986464509605811)
      ·
        refine ⟨3055405594479696764408717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2036937062986464509605811 3055405594479696764408717)
        ·
          refine ⟨1145777097929886286653269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3055405594479696764408717 1145777097929886286653269)
          ·
            refine ⟨6713537683182927460859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1145777097929886286653269 6713537683182927460859)
            ·
              rfl

theorem cell20_397140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 9].length) (baseStart_397140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397140 prefixEnd_397140 := by exact prefixLift 397140
  have htrace : WordTrace (prefixWord ++ tailWord_397140) baseStart_397140 baseEnd_397140 := by
    simpa [prefixWord, tailWord_397140, baseEnd_397140] using wordTrace_append hprefix tailTrace_397140
  have hstable : (prefixWord ++ tailWord_397140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397140).length < 2 ^ (prefixWord ++ tailWord_397140).sum := by decide
  have hdescent : baseEnd_397140 < baseStart_397140 := by decide
  rcases family_descends (prefixWord ++ tailWord_397140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397143 : List Nat := [1, 1, 3, 2, 5, 1, 2, 2, 3]
def baseStart_397143 : Nat := 118140960795 + 397143 * 2 ^ 59
def prefixEnd_397143 : Nat := 4983230072969 + 3 ^ 40 * 397143 * 2
def baseEnd_397143 : Nat := 181266886727684364343181

theorem tailTrace_397143 : CollatzResearch.WordTrace tailWord_397143 prefixEnd_397143 181266886727684364343181 := by
  unfold tailWord_397143
  simp only [CollatzResearch.WordTrace]
  refine ⟨14484995200226212469556083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9656663466817474979704055 14484995200226212469556083)
  ·
    refine ⟨21727492800339318704334125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14484995200226212469556083 21727492800339318704334125)
    ·
      refine ⟨8147809800127244514125297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21727492800339318704334125 8147809800127244514125297)
      ·
        refine ⟨6110857350095433385593973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8147809800127244514125297 6110857350095433385593973)
        ·
          refine ⟨572892876571446879899435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6110857350095433385593973 572892876571446879899435)
          ·
            refine ⟨859339314857170319849153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572892876571446879899435 859339314857170319849153)
            ·
              refine ⟨644504486142877739886865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 859339314857170319849153 644504486142877739886865)
              ·
                refine ⟨483378364607158304915149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 644504486142877739886865 483378364607158304915149)
                ·
                  refine ⟨181266886727684364343181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483378364607158304915149 181266886727684364343181)
                  ·
                    rfl

theorem cell20_397143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 3].length) (baseStart_397143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397143 prefixEnd_397143 := by exact prefixLift 397143
  have htrace : WordTrace (prefixWord ++ tailWord_397143) baseStart_397143 baseEnd_397143 := by
    simpa [prefixWord, tailWord_397143, baseEnd_397143] using wordTrace_append hprefix tailTrace_397143
  have hstable : (prefixWord ++ tailWord_397143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397143).length < 2 ^ (prefixWord ++ tailWord_397143).sum := by decide
  have hdescent : baseEnd_397143 < baseStart_397143 := by decide
  rcases family_descends (prefixWord ++ tailWord_397143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397164 : List Nat := [2, 2, 1, 1, 4, 2, 2, 3, 3]
def baseStart_397164 : Nat := 118140960795 + 397164 * 2 ^ 59
def prefixEnd_397164 : Nat := 4983230072969 + 3 ^ 40 * 397164 * 2
def baseEnd_397164 : Nat := 181276471699901624643095

theorem tailTrace_397164 : CollatzResearch.WordTrace tailWord_397164 prefixEnd_397164 181276471699901624643095 := by
  unfold tailWord_397164
  simp only [CollatzResearch.WordTrace]
  refine ⟨7242880566575066528035273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9657174088766755370713697 7242880566575066528035273)
  ·
    refine ⟨5432160424931299896026455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7242880566575066528035273 5432160424931299896026455)
    ·
      refine ⟨8148240637396949844039683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5432160424931299896026455 8148240637396949844039683)
      ·
        refine ⟨12222360956095424766059525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8148240637396949844039683 12222360956095424766059525)
        ·
          refine ⟨2291692679267892143636161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12222360956095424766059525 2291692679267892143636161)
          ·
            refine ⟨1718769509450919107727121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2291692679267892143636161 1718769509450919107727121)
            ·
              refine ⟨1289077132088189330795341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1718769509450919107727121 1289077132088189330795341)
              ·
                refine ⟨483403924533070999048253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1289077132088189330795341 483403924533070999048253)
                ·
                  refine ⟨181276471699901624643095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483403924533070999048253 181276471699901624643095)
                  ·
                    rfl

theorem cell20_397164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_397164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397164 prefixEnd_397164 := by exact prefixLift 397164
  have htrace : WordTrace (prefixWord ++ tailWord_397164) baseStart_397164 baseEnd_397164 := by
    simpa [prefixWord, tailWord_397164, baseEnd_397164] using wordTrace_append hprefix tailTrace_397164
  have hstable : (prefixWord ++ tailWord_397164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397164).length < 2 ^ (prefixWord ++ tailWord_397164).sum := by decide
  have hdescent : baseEnd_397164 < baseStart_397164 := by decide
  rcases family_descends (prefixWord ++ tailWord_397164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397188 : List Nat := [2, 3, 2, 1, 1, 1, 3, 5, 2]
def baseStart_397188 : Nat := 118140960795 + 397188 * 2 ^ 59
def prefixEnd_397188 : Nat := 4983230072969 + 3 ^ 40 * 397188 * 2
def baseEnd_397188 : Nat := 181287425953864207842997

theorem tailTrace_397188 : CollatzResearch.WordTrace tailWord_397188 prefixEnd_397188 181287425953864207842997 := by
  unfold tailWord_397188
  simp only [CollatzResearch.WordTrace]
  refine ⟨7243318242531592577472109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9657757656708790103296145 7243318242531592577472109)
  ·
    refine ⟨2716244340949347216552041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7243318242531592577472109 2716244340949347216552041)
    ·
      refine ⟨2037183255712010412414031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2716244340949347216552041 2037183255712010412414031)
      ·
        refine ⟨3055774883568015618621047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2037183255712010412414031 3055774883568015618621047)
        ·
          refine ⟨4583662325352023427931571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055774883568015618621047 4583662325352023427931571)
          ·
            refine ⟨6875493488028035141897357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583662325352023427931571 6875493488028035141897357)
            ·
              refine ⟨2578310058010513178211509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6875493488028035141897357 2578310058010513178211509)
              ·
                refine ⟨241716567938485610457329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2578310058010513178211509 241716567938485610457329)
                ·
                  refine ⟨181287425953864207842997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241716567938485610457329 181287425953864207842997)
                  ·
                    rfl

theorem cell20_397188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_397188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397188 prefixEnd_397188 := by exact prefixLift 397188
  have htrace : WordTrace (prefixWord ++ tailWord_397188) baseStart_397188 baseEnd_397188 := by
    simpa [prefixWord, tailWord_397188, baseEnd_397188] using wordTrace_append hprefix tailTrace_397188
  have hstable : (prefixWord ++ tailWord_397188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397188).length < 2 ^ (prefixWord ++ tailWord_397188).sum := by decide
  have hdescent : baseEnd_397188 < baseStart_397188 := by decide
  rcases family_descends (prefixWord ++ tailWord_397188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397233 : List Nat := [1, 2, 2, 4, 2, 1, 4, 4]
def baseStart_397233 : Nat := 118140960795 + 397233 * 2 ^ 59
def prefixEnd_397233 : Nat := 4983230072969 + 3 ^ 40 * 397233 * 2
def baseEnd_397233 : Nat := 60435988393348017114271

theorem tailTrace_397233 : CollatzResearch.WordTrace tailWord_397233 prefixEnd_397233 60435988393348017114271 := by
  unfold tailWord_397233
  simp only [CollatzResearch.WordTrace]
  refine ⟨14488277769900157840332353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9658851846600105226888235 14488277769900157840332353)
  ·
    refine ⟨10866208327425118380249265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14488277769900157840332353 10866208327425118380249265)
    ·
      refine ⟨8149656245568838785186949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10866208327425118380249265 8149656245568838785186949)
      ·
        refine ⟨1528060546044157272222553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8149656245568838785186949 1528060546044157272222553)
        ·
          refine ⟨1146045409533117954166915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1528060546044157272222553 1146045409533117954166915)
          ·
            refine ⟨1719068114299676931250373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146045409533117954166915 1719068114299676931250373)
            ·
              refine ⟨322325271431189424609445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1719068114299676931250373 322325271431189424609445)
              ·
                refine ⟨60435988393348017114271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322325271431189424609445 60435988393348017114271)
                ·
                  rfl

theorem cell20_397233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 4].length) (baseStart_397233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397233 prefixEnd_397233 := by exact prefixLift 397233
  have htrace : WordTrace (prefixWord ++ tailWord_397233) baseStart_397233 baseEnd_397233 := by
    simpa [prefixWord, tailWord_397233, baseEnd_397233] using wordTrace_append hprefix tailTrace_397233
  have hstable : (prefixWord ++ tailWord_397233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397233).length < 2 ^ (prefixWord ++ tailWord_397233).sum := by decide
  have hdescent : baseEnd_397233 < baseStart_397233 := by decide
  rcases family_descends (prefixWord ++ tailWord_397233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397270 : List Nat := [5, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_397270 : Nat := 118140960795 + 397270 * 2 ^ 59
def prefixEnd_397270 : Nat := 4983230072969 + 3 ^ 40 * 397270 * 2
def baseEnd_397270 : Nat := 181324852988236367109329

theorem tailTrace_397270 : CollatzResearch.WordTrace tailWord_397270 prefixEnd_397270 181324852988236367109329 := by
  unfold tailWord_397270
  simp only [CollatzResearch.WordTrace]
  refine ⟨905601704422882072464329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9659751513844075439619509 905601704422882072464329)
  ·
    refine ⟨679201278317161554348247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 905601704422882072464329 679201278317161554348247)
    ·
      refine ⟨1018801917475742331522371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 679201278317161554348247 1018801917475742331522371)
      ·
        refine ⟨1528202876213613497283557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1018801917475742331522371 1528202876213613497283557)
        ·
          refine ⟨286538039290052530740667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1528202876213613497283557 286538039290052530740667)
          ·
            refine ⟨429807058935078796111001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286538039290052530740667 429807058935078796111001)
            ·
              refine ⟨322355294201309097083251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429807058935078796111001 322355294201309097083251)
              ·
                refine ⟨483532941301963645624877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322355294201309097083251 483532941301963645624877)
                ·
                  refine ⟨181324852988236367109329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483532941301963645624877 181324852988236367109329)
                  ·
                    rfl

theorem cell20_397270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_397270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397270 prefixEnd_397270 := by exact prefixLift 397270
  have htrace : WordTrace (prefixWord ++ tailWord_397270) baseStart_397270 baseEnd_397270 := by
    simpa [prefixWord, tailWord_397270, baseEnd_397270] using wordTrace_append hprefix tailTrace_397270
  have hstable : (prefixWord ++ tailWord_397270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397270).length < 2 ^ (prefixWord ++ tailWord_397270).sum := by decide
  have hdescent : baseEnd_397270 < baseStart_397270 := by decide
  rcases family_descends (prefixWord ++ tailWord_397270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397274 : List Nat := [3, 1, 1, 2, 5, 2, 2, 1, 3]
def baseStart_397274 : Nat := 118140960795 + 397274 * 2 ^ 59
def prefixEnd_397274 : Nat := 4983230072969 + 3 ^ 40 * 397274 * 2
def baseEnd_397274 : Nat := 181326678697230130975979

theorem tailTrace_397274 : CollatzResearch.WordTrace tailWord_397274 prefixEnd_397274 181326678697230130975979 := by
  unfold tailWord_397274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3622443290687905460643719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9659848775167747895049917 3622443290687905460643719)
  ·
    refine ⟨5433664936031858190965579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3622443290687905460643719 5433664936031858190965579)
    ·
      refine ⟨8150497404047787286448369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5433664936031858190965579 8150497404047787286448369)
      ·
        refine ⟨6112873053035840464836277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8150497404047787286448369 6112873053035840464836277)
        ·
          refine ⟨573081848722110043578401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6112873053035840464836277 573081848722110043578401)
          ·
            refine ⟨429811386541582532683801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 573081848722110043578401 429811386541582532683801)
            ·
              refine ⟨322358539906186899512851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429811386541582532683801 322358539906186899512851)
              ·
                refine ⟨483537809859280349269277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322358539906186899512851 483537809859280349269277)
                ·
                  refine ⟨181326678697230130975979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483537809859280349269277 181326678697230130975979)
                  ·
                    rfl

theorem cell20_397274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_397274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397274 prefixEnd_397274 := by exact prefixLift 397274
  have htrace : WordTrace (prefixWord ++ tailWord_397274) baseStart_397274 baseEnd_397274 := by
    simpa [prefixWord, tailWord_397274, baseEnd_397274] using wordTrace_append hprefix tailTrace_397274
  have hstable : (prefixWord ++ tailWord_397274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397274).length < 2 ^ (prefixWord ++ tailWord_397274).sum := by decide
  have hdescent : baseEnd_397274 < baseStart_397274 := by decide
  rcases family_descends (prefixWord ++ tailWord_397274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397319 : List Nat := [1, 1, 4, 3, 1, 2, 4, 2, 2]
def baseStart_397319 : Nat := 118140960795 + 397319 * 2 ^ 59
def prefixEnd_397319 : Nat := 4983230072969 + 3 ^ 40 * 397319 * 2
def baseEnd_397319 : Nat := 181347217923409974475795

theorem tailTrace_397319 : CollatzResearch.WordTrace tailWord_397319 prefixEnd_397319 181347217923409974475795 := by
  unfold tailWord_397319
  simp only [CollatzResearch.WordTrace]
  refine ⟨14491414447588594527963011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9660942965059063018642007 14491414447588594527963011)
  ·
    refine ⟨21737121671382891791944517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14491414447588594527963011 21737121671382891791944517)
    ·
      refine ⟨4075710313384292210989597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21737121671382891791944517 4075710313384292210989597)
      ·
        refine ⟨1528391367519109579121099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4075710313384292210989597 1528391367519109579121099)
        ·
          refine ⟨2292587051278664368681649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1528391367519109579121099 2292587051278664368681649)
          ·
            refine ⟨1719440288458998276511237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2292587051278664368681649 1719440288458998276511237)
            ·
              refine ⟨322395054086062176845857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1719440288458998276511237 322395054086062176845857)
              ·
                refine ⟨241796290564546632634393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322395054086062176845857 241796290564546632634393)
                ·
                  refine ⟨181347217923409974475795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241796290564546632634393 181347217923409974475795)
                  ·
                    rfl

theorem cell20_397319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 2].length) (baseStart_397319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397319 prefixEnd_397319 := by exact prefixLift 397319
  have htrace : WordTrace (prefixWord ++ tailWord_397319) baseStart_397319 baseEnd_397319 := by
    simpa [prefixWord, tailWord_397319, baseEnd_397319] using wordTrace_append hprefix tailTrace_397319
  have hstable : (prefixWord ++ tailWord_397319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397319).length < 2 ^ (prefixWord ++ tailWord_397319).sum := by decide
  have hdescent : baseEnd_397319 < baseStart_397319 := by decide
  rcases family_descends (prefixWord ++ tailWord_397319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397368 : List Nat := [2, 1, 2, 1, 6, 1, 7]
def baseStart_397368 : Nat := 118140960795 + 397368 * 2 ^ 59
def prefixEnd_397368 : Nat := 4983230072969 + 3 ^ 40 * 397368 * 2
def baseEnd_397368 : Nat := 20152175873175953538029

theorem tailTrace_397368 : CollatzResearch.WordTrace tailWord_397368 prefixEnd_397368 20152175873175953538029 := by
  unfold tailWord_397368
  simp only [CollatzResearch.WordTrace]
  refine ⟨7246600812205537948248379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9662134416274050597664505 7246600812205537948248379)
  ·
    refine ⟨10869901218308306922372569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7246600812205537948248379 10869901218308306922372569)
    ·
      refine ⟨8152425913731230191779427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10869901218308306922372569 8152425913731230191779427)
      ·
        refine ⟨12228638870596845287669141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8152425913731230191779427 12228638870596845287669141)
        ·
          refine ⟨573217447059227122859491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12228638870596845287669141 573217447059227122859491)
          ·
            refine ⟨859826170588840684289237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573217447059227122859491 859826170588840684289237)
            ·
              refine ⟨20152175873175953538029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 859826170588840684289237 20152175873175953538029)
              ·
                rfl

theorem cell20_397368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 7].length) (baseStart_397368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397368 prefixEnd_397368 := by exact prefixLift 397368
  have htrace : WordTrace (prefixWord ++ tailWord_397368) baseStart_397368 baseEnd_397368 := by
    simpa [prefixWord, tailWord_397368, baseEnd_397368] using wordTrace_append hprefix tailTrace_397368
  have hstable : (prefixWord ++ tailWord_397368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397368).length < 2 ^ (prefixWord ++ tailWord_397368).sum := by decide
  have hdescent : baseEnd_397368 < baseStart_397368 := by decide
  rcases family_descends (prefixWord ++ tailWord_397368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397413 : List Nat := [1, 3, 1, 3, 2, 2, 1, 2, 5]
def baseStart_397413 : Nat := 118140960795 + 397413 * 2 ^ 59
def prefixEnd_397413 : Nat := 4983230072969 + 3 ^ 40 * 397413 * 2
def baseEnd_397413 : Nat := 181390122084763425342077

theorem tailTrace_397413 : CollatzResearch.WordTrace tailWord_397413 prefixEnd_397413 181390122084763425342077 := by
  unfold tailWord_397413
  simp only [CollatzResearch.WordTrace]
  refine ⟨14494842909248048581884893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9663228606165365721256595 14494842909248048581884893)
  ·
    refine ⟨5435566090968018218206835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14494842909248048581884893 5435566090968018218206835)
    ·
      refine ⟨8153349136452027327310253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5435566090968018218206835 8153349136452027327310253)
      ·
        refine ⟨3057505926169510247741345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8153349136452027327310253 3057505926169510247741345)
        ·
          refine ⟨2293129444627132685806009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3057505926169510247741345 2293129444627132685806009)
          ·
            refine ⟨1719847083470349514354507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2293129444627132685806009 1719847083470349514354507)
            ·
              refine ⟨2579770625205524271531761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1719847083470349514354507 2579770625205524271531761)
              ·
                refine ⟨1934827968904143203648821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2579770625205524271531761 1934827968904143203648821)
                ·
                  refine ⟨181390122084763425342077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1934827968904143203648821 181390122084763425342077)
                  ·
                    rfl

theorem cell20_397413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_397413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397413 prefixEnd_397413 := by exact prefixLift 397413
  have htrace : WordTrace (prefixWord ++ tailWord_397413) baseStart_397413 baseEnd_397413 := by
    simpa [prefixWord, tailWord_397413, baseEnd_397413] using wordTrace_append hprefix tailTrace_397413
  have hstable : (prefixWord ++ tailWord_397413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397413).length < 2 ^ (prefixWord ++ tailWord_397413).sum := by decide
  have hdescent : baseEnd_397413 < baseStart_397413 := by decide
  rcases family_descends (prefixWord ++ tailWord_397413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397430 : List Nat := [5, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_397430 : Nat := 118140960795 + 397430 * 2 ^ 59
def prefixEnd_397430 : Nat := 4983230072969 + 3 ^ 40 * 397430 * 2
def baseEnd_397430 : Nat := 181397881347986921775341

theorem tailTrace_397430 : CollatzResearch.WordTrace tailWord_397430 prefixEnd_397430 181397881347986921775341 := by
  unfold tailWord_397430
  simp only [CollatzResearch.WordTrace]
  refine ⟨905966434386653780328359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9663641966790973656835829 905966434386653780328359)
  ·
    refine ⟨1358949651579980670492539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 905966434386653780328359 1358949651579980670492539)
    ·
      refine ⟨2038424477369971005738809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1358949651579980670492539 2038424477369971005738809)
      ·
        refine ⟨1528818358027478254304107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2038424477369971005738809 1528818358027478254304107)
        ·
          refine ⟨2293227537041217381456161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1528818358027478254304107 2293227537041217381456161)
          ·
            refine ⟨1719920652780913036092121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2293227537041217381456161 1719920652780913036092121)
            ·
              refine ⟨1289940489585684777069091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1719920652780913036092121 1289940489585684777069091)
              ·
                refine ⟨1934910734378527165603637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289940489585684777069091 1934910734378527165603637)
                ·
                  refine ⟨181397881347986921775341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1934910734378527165603637 181397881347986921775341)
                  ·
                    rfl

theorem cell20_397430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_397430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397430 prefixEnd_397430 := by exact prefixLift 397430
  have htrace : WordTrace (prefixWord ++ tailWord_397430) baseStart_397430 baseEnd_397430 := by
    simpa [prefixWord, tailWord_397430, baseEnd_397430] using wordTrace_append hprefix tailTrace_397430
  have hstable : (prefixWord ++ tailWord_397430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397430).length < 2 ^ (prefixWord ++ tailWord_397430).sum := by decide
  have hdescent : baseEnd_397430 < baseStart_397430 := by decide
  rcases family_descends (prefixWord ++ tailWord_397430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397433 : List Nat := [1, 2, 1, 3, 4, 2, 3, 2, 2]
def baseStart_397433 : Nat := 118140960795 + 397433 * 2 ^ 59
def prefixEnd_397433 : Nat := 4983230072969 + 3 ^ 40 * 397433 * 2
def baseEnd_397433 : Nat := 181399250629732244675329

theorem tailTrace_397433 : CollatzResearch.WordTrace tailWord_397433 prefixEnd_397433 181399250629732244675329 := by
  unfold tailWord_397433
  simp only [CollatzResearch.WordTrace]
  refine ⟨14495572369175591997612953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9663714912783727998408635 14495572369175591997612953)
  ·
    refine ⟨10871679276881693998209715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14495572369175591997612953 10871679276881693998209715)
    ·
      refine ⟨16307518915322540997314573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10871679276881693998209715 16307518915322540997314573)
      ·
        refine ⟨6115319593245952873992965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16307518915322540997314573 6115319593245952873992965)
        ·
          refine ⟨1146622423733616163873681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6115319593245952873992965 1146622423733616163873681)
          ·
            refine ⟨859966817800212122905261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1146622423733616163873681 859966817800212122905261)
            ·
              refine ⟨322487556675079546089473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 859966817800212122905261 322487556675079546089473)
              ·
                refine ⟨241865667506309659567105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322487556675079546089473 241865667506309659567105)
                ·
                  refine ⟨181399250629732244675329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241865667506309659567105 181399250629732244675329)
                  ·
                    rfl

theorem cell20_397433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 2].length) (baseStart_397433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397433 prefixEnd_397433 := by exact prefixLift 397433
  have htrace : WordTrace (prefixWord ++ tailWord_397433) baseStart_397433 baseEnd_397433 := by
    simpa [prefixWord, tailWord_397433, baseEnd_397433] using wordTrace_append hprefix tailTrace_397433
  have hstable : (prefixWord ++ tailWord_397433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397433).length < 2 ^ (prefixWord ++ tailWord_397433).sum := by decide
  have hdescent : baseEnd_397433 < baseStart_397433 := by decide
  rcases family_descends (prefixWord ++ tailWord_397433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397437 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 4]
def baseStart_397437 : Nat := 118140960795 + 397437 * 2 ^ 59
def prefixEnd_397437 : Nat := 4983230072969 + 3 ^ 40 * 397437 * 2
def baseEnd_397437 : Nat := 181401076338726008541979

theorem tailTrace_397437 : CollatzResearch.WordTrace tailWord_397437 prefixEnd_397437 181401076338726008541979 := by
  unfold tailWord_397437
  simp only [CollatzResearch.WordTrace]
  refine ⟨14495718261161100680758565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9663812174107400453839043 14495718261161100680758565)
  ·
    refine ⟨2717947173967706377642231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14495718261161100680758565 2717947173967706377642231)
    ·
      refine ⟨4076920760951559566463347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2717947173967706377642231 4076920760951559566463347)
      ·
        refine ⟨6115381141427339349695021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4076920760951559566463347 6115381141427339349695021)
        ·
          refine ⟨2293267928035252256135633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6115381141427339349695021 2293267928035252256135633)
          ·
            refine ⟨1719950946026439192101725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2293267928035252256135633 1719950946026439192101725)
            ·
              refine ⟨644981604759914697038147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1719950946026439192101725 644981604759914697038147)
              ·
                refine ⟨967472407139872045557221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644981604759914697038147 967472407139872045557221)
                ·
                  refine ⟨181401076338726008541979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 967472407139872045557221 181401076338726008541979)
                  ·
                    rfl

theorem cell20_397437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_397437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397437 prefixEnd_397437 := by exact prefixLift 397437
  have htrace : WordTrace (prefixWord ++ tailWord_397437) baseStart_397437 baseEnd_397437 := by
    simpa [prefixWord, tailWord_397437, baseEnd_397437] using wordTrace_append hprefix tailTrace_397437
  have hstable : (prefixWord ++ tailWord_397437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397437).length < 2 ^ (prefixWord ++ tailWord_397437).sum := by decide
  have hdescent : baseEnd_397437 < baseStart_397437 := by decide
  rcases family_descends (prefixWord ++ tailWord_397437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397444 : List Nat := [2, 3, 2, 1, 2, 1, 4, 5]
def baseStart_397444 : Nat := 118140960795 + 397444 * 2 ^ 59
def prefixEnd_397444 : Nat := 4983230072969 + 3 ^ 40 * 397444 * 2
def baseEnd_397444 : Nat := 60468090443155031769539

theorem tailTrace_397444 : CollatzResearch.WordTrace tailWord_397444 prefixEnd_397444 60468090443155031769539 := by
  unfold tailWord_397444
  simp only [CollatzResearch.WordTrace]
  refine ⟨7247986786067870438131693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9663982381423827250842257 7247986786067870438131693)
  ·
    refine ⟨2717995044775451414299385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7247986786067870438131693 2717995044775451414299385)
    ·
      refine ⟨2038496283581588560724539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2717995044775451414299385 2038496283581588560724539)
      ·
        refine ⟨3057744425372382841086809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2038496283581588560724539 3057744425372382841086809)
        ·
          refine ⟨2293308319029287130815107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3057744425372382841086809 2293308319029287130815107)
          ·
            refine ⟨3439962478543930696222661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2293308319029287130815107 3439962478543930696222661)
            ·
              refine ⟨644992964726987005541749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3439962478543930696222661 644992964726987005541749)
              ·
                refine ⟨60468090443155031769539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 644992964726987005541749 60468090443155031769539)
                ·
                  rfl

theorem cell20_397444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_397444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397444 prefixEnd_397444 := by exact prefixLift 397444
  have htrace : WordTrace (prefixWord ++ tailWord_397444) baseStart_397444 baseEnd_397444 := by
    simpa [prefixWord, tailWord_397444, baseEnd_397444] using wordTrace_append hprefix tailTrace_397444
  have hstable : (prefixWord ++ tailWord_397444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397444).length < 2 ^ (prefixWord ++ tailWord_397444).sum := by decide
  have hdescent : baseEnd_397444 < baseStart_397444 := by decide
  rcases family_descends (prefixWord ++ tailWord_397444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397482 : List Nat := [3, 1, 5, 1, 10]
def baseStart_397482 : Nat := 118140960795 + 397482 * 2 ^ 59
def prefixEnd_397482 : Nat := 4983230072969 + 3 ^ 40 * 397482 * 2
def baseEnd_397482 : Nat := 2239773031665504346195

theorem tailTrace_397482 : CollatzResearch.WordTrace tailWord_397482 prefixEnd_397482 2239773031665504346195 := by
  unfold tailWord_397482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3624339886499518341536675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9664906363998715577431133 3624339886499518341536675)
  ·
    refine ⟨5436509829749277512305013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3624339886499518341536675 5436509829749277512305013)
    ·
      refine ⟨509672796538994766778595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5436509829749277512305013 509672796538994766778595)
      ·
        refine ⟨764509194808492150167893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509672796538994766778595 764509194808492150167893)
        ·
          refine ⟨2239773031665504346195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 764509194808492150167893 2239773031665504346195)
          ·
            rfl

theorem cell20_397482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 10].length) (baseStart_397482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397482 prefixEnd_397482 := by exact prefixLift 397482
  have htrace : WordTrace (prefixWord ++ tailWord_397482) baseStart_397482 baseEnd_397482 := by
    simpa [prefixWord, tailWord_397482, baseEnd_397482] using wordTrace_append hprefix tailTrace_397482
  have hstable : (prefixWord ++ tailWord_397482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397482).length < 2 ^ (prefixWord ++ tailWord_397482).sum := by decide
  have hdescent : baseEnd_397482 < baseStart_397482 := by decide
  rcases family_descends (prefixWord ++ tailWord_397482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397485 : List Nat := [1, 5, 2, 1, 2, 2, 2, 2, 3]
def baseStart_397485 : Nat := 118140960795 + 397485 * 2 ^ 59
def prefixEnd_397485 : Nat := 4983230072969 + 3 ^ 40 * 397485 * 2
def baseEnd_397485 : Nat := 181422984846651174941783

theorem tailTrace_397485 : CollatzResearch.WordTrace tailWord_397485 prefixEnd_397485 181422984846651174941783 := by
  unfold tailWord_397485
  simp only [CollatzResearch.WordTrace]
  refine ⟨14497468964987204878505909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9664979309991469919003939 14497468964987204878505909)
  ·
    refine ⟨1359137715467550457359929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14497468964987204878505909 1359137715467550457359929)
    ·
      refine ⟨1019353286600662843019947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1359137715467550457359929 1019353286600662843019947)
      ·
        refine ⟨1529029929900994264529921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1019353286600662843019947 1529029929900994264529921)
        ·
          refine ⟨1146772447425745698397441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1529029929900994264529921 1146772447425745698397441)
          ·
            refine ⟨860079335569309273798081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1146772447425745698397441 860079335569309273798081)
            ·
              refine ⟨645059501676981955348561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 860079335569309273798081 645059501676981955348561)
              ·
                refine ⟨483794626257736466511421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645059501676981955348561 483794626257736466511421)
                ·
                  refine ⟨181422984846651174941783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483794626257736466511421 181422984846651174941783)
                  ·
                    rfl

theorem cell20_397485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_397485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397485 prefixEnd_397485 := by exact prefixLift 397485
  have htrace : WordTrace (prefixWord ++ tailWord_397485) baseStart_397485 baseEnd_397485 := by
    simpa [prefixWord, tailWord_397485, baseEnd_397485] using wordTrace_append hprefix tailTrace_397485
  have hstable : (prefixWord ++ tailWord_397485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397485).length < 2 ^ (prefixWord ++ tailWord_397485).sum := by decide
  have hdescent : baseEnd_397485 < baseStart_397485 := by decide
  rcases family_descends (prefixWord ++ tailWord_397485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397496 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 4]
def baseStart_397496 : Nat := 118140960795 + 397496 * 2 ^ 59
def prefixEnd_397496 : Nat := 4983230072969 + 3 ^ 40 * 397496 * 2
def baseEnd_397496 : Nat := 181428005546384025575071

theorem tailTrace_397496 : CollatzResearch.WordTrace tailWord_397496 prefixEnd_397496 181428005546384025575071 := by
  unfold tailWord_397496
  simp only [CollatzResearch.WordTrace]
  refine ⟨7248935083973676878578171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9665246778631569171437561 7248935083973676878578171)
  ·
    refine ⟨10873402625960515317867257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7248935083973676878578171 10873402625960515317867257)
    ·
      refine ⟨8155051969470386488400443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10873402625960515317867257 8155051969470386488400443)
      ·
        refine ⟨12232577954205579732600665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8155051969470386488400443 12232577954205579732600665)
        ·
          refine ⟨9174433465654184799450499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12232577954205579732600665 9174433465654184799450499)
          ·
            refine ⟨13761650198481277199175749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9174433465654184799450499 13761650198481277199175749)
            ·
              refine ⟨2580309412215239474845453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13761650198481277199175749 2580309412215239474845453)
              ·
                refine ⟨967616029580714803067045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2580309412215239474845453 967616029580714803067045)
                ·
                  refine ⟨181428005546384025575071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 967616029580714803067045 181428005546384025575071)
                  ·
                    rfl

theorem cell20_397496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_397496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397496 prefixEnd_397496 := by exact prefixLift 397496
  have htrace : WordTrace (prefixWord ++ tailWord_397496) baseStart_397496 baseEnd_397496 := by
    simpa [prefixWord, tailWord_397496, baseEnd_397496] using wordTrace_append hprefix tailTrace_397496
  have hstable : (prefixWord ++ tailWord_397496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397496).length < 2 ^ (prefixWord ++ tailWord_397496).sum := by decide
  have hdescent : baseEnd_397496 < baseStart_397496 := by decide
  rcases family_descends (prefixWord ++ tailWord_397496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397516 : List Nat := [2, 2, 1, 6, 1, 1, 3, 4]
def baseStart_397516 : Nat := 118140960795 + 397516 * 2 ^ 59
def prefixEnd_397516 : Nat := 4983230072969 + 3 ^ 40 * 397516 * 2
def baseEnd_397516 : Nat := 60479044697117614969441

theorem tailTrace_397516 : CollatzResearch.WordTrace tailWord_397516 prefixEnd_397516 60479044697117614969441 := by
  unfold tailWord_397516
  simp only [CollatzResearch.WordTrace]
  refine ⟨7249299813937448586442201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9665733085249931448589601 7249299813937448586442201)
  ·
    refine ⟨5436974860453086439831651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7249299813937448586442201 5436974860453086439831651)
    ·
      refine ⟨8155462290679629659747477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5436974860453086439831651 8155462290679629659747477)
      ·
        refine ⟨382287294875607640300663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8155462290679629659747477 382287294875607640300663)
        ·
          refine ⟨573430942313411460450995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382287294875607640300663 573430942313411460450995)
          ·
            refine ⟨860146413470117190676493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573430942313411460450995 860146413470117190676493)
            ·
              refine ⟨322554905051293946503685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 860146413470117190676493 322554905051293946503685)
              ·
                refine ⟨60479044697117614969441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322554905051293946503685 60479044697117614969441)
                ·
                  rfl

theorem cell20_397516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_397516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397516 prefixEnd_397516 := by exact prefixLift 397516
  have htrace : WordTrace (prefixWord ++ tailWord_397516) baseStart_397516 baseEnd_397516 := by
    simpa [prefixWord, tailWord_397516, baseEnd_397516] using wordTrace_append hprefix tailTrace_397516
  have hstable : (prefixWord ++ tailWord_397516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397516).length < 2 ^ (prefixWord ++ tailWord_397516).sum := by decide
  have hdescent : baseEnd_397516 < baseStart_397516 := by decide
  rcases family_descends (prefixWord ++ tailWord_397516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397526 : List Nat := [5, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_397526 : Nat := 118140960795 + 397526 * 2 ^ 59
def prefixEnd_397526 : Nat := 4983230072969 + 3 ^ 40 * 397526 * 2
def baseEnd_397526 : Nat := 181441698363837254574949

theorem tailTrace_397526 : CollatzResearch.WordTrace tailWord_397526 prefixEnd_397526 181441698363837254574949 := by
  unfold tailWord_397526
  simp only [CollatzResearch.WordTrace]
  refine ⟨906185272364916805046777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9665976238559112587165621 906185272364916805046777)
  ·
    refine ⟨679638954273687603785083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 906185272364916805046777 679638954273687603785083)
    ·
      refine ⟨1019458431410531405677625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 679638954273687603785083 1019458431410531405677625)
      ·
        refine ⟨764593823557898554258219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1019458431410531405677625 764593823557898554258219)
        ·
          refine ⟨1146890735336847831387329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764593823557898554258219 1146890735336847831387329)
          ·
            refine ⟨860168051502635873540497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1146890735336847831387329 860168051502635873540497)
            ·
              refine ⟨645126038626976905155373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 860168051502635873540497 645126038626976905155373)
              ·
                refine ⟨241922264485116339433265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 645126038626976905155373 241922264485116339433265)
                ·
                  refine ⟨181441698363837254574949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241922264485116339433265 181441698363837254574949)
                  ·
                    rfl

theorem cell20_397526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_397526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397526 prefixEnd_397526 := by exact prefixLift 397526
  have htrace : WordTrace (prefixWord ++ tailWord_397526) baseStart_397526 baseEnd_397526 := by
    simpa [prefixWord, tailWord_397526, baseEnd_397526] using wordTrace_append hprefix tailTrace_397526
  have hstable : (prefixWord ++ tailWord_397526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397526).length < 2 ^ (prefixWord ++ tailWord_397526).sum := by decide
  have hdescent : baseEnd_397526 < baseStart_397526 := by decide
  rcases family_descends (prefixWord ++ tailWord_397526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397544 : List Nat := [2, 1, 4, 1, 2, 2, 3, 2, 3]
def baseStart_397544 : Nat := 118140960795 + 397544 * 2 ^ 59
def prefixEnd_397544 : Nat := 4983230072969 + 3 ^ 40 * 397544 * 2
def baseEnd_397544 : Nat := 181449914054309191974875

theorem tailTrace_397544 : CollatzResearch.WordTrace tailWord_397544 prefixEnd_397544 181449914054309191974875 := by
  unfold tailWord_397544
  simp only [CollatzResearch.WordTrace]
  refine ⟨7249810435886728977451843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9666413914515638636602457 7249810435886728977451843)
  ·
    refine ⟨10874715653830093466177765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7249810435886728977451843 10874715653830093466177765)
    ·
      refine ⟨2039009185093142524908331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10874715653830093466177765 2039009185093142524908331)
      ·
        refine ⟨3058513777639713787362497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2039009185093142524908331 3058513777639713787362497)
        ·
          refine ⟨2293885333229785340521873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3058513777639713787362497 2293885333229785340521873)
          ·
            refine ⟨1720413999922339005391405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2293885333229785340521873 1720413999922339005391405)
            ·
              refine ⟨645155249970877127021777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1720413999922339005391405 645155249970877127021777)
              ·
                refine ⟨483866437478157845266333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645155249970877127021777 483866437478157845266333)
                ·
                  refine ⟨181449914054309191974875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483866437478157845266333 181449914054309191974875)
                  ·
                    rfl

theorem cell20_397544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_397544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397544 prefixEnd_397544 := by exact prefixLift 397544
  have htrace : WordTrace (prefixWord ++ tailWord_397544) baseStart_397544 baseEnd_397544 := by
    simpa [prefixWord, tailWord_397544, baseEnd_397544] using wordTrace_append hprefix tailTrace_397544
  have hstable : (prefixWord ++ tailWord_397544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397544).length < 2 ^ (prefixWord ++ tailWord_397544).sum := by decide
  have hdescent : baseEnd_397544 < baseStart_397544 := by decide
  rcases family_descends (prefixWord ++ tailWord_397544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397551 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 4]
def baseStart_397551 : Nat := 118140960795 + 397551 * 2 ^ 59
def prefixEnd_397551 : Nat := 4983230072969 + 3 ^ 40 * 397551 * 2
def baseEnd_397551 : Nat := 181453109045048278741513

theorem tailTrace_397551 : CollatzResearch.WordTrace tailWord_397551 prefixEnd_397551 181453109045048278741513 := by
  unfold tailWord_397551
  simp only [CollatzResearch.WordTrace]
  refine ⟨14499876182748098150408507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9666584121832065433605671 14499876182748098150408507)
  ·
    refine ⟨21749814274122147225612761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14499876182748098150408507 21749814274122147225612761)
    ·
      refine ⟨16312360705591610419209571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21749814274122147225612761 16312360705591610419209571)
      ·
        refine ⟨24468541058387415628814357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16312360705591610419209571 24468541058387415628814357)
        ·
          refine ⟨1146962862111910107600673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24468541058387415628814357 1146962862111910107600673)
          ·
            refine ⟨860222146583932580700505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1146962862111910107600673 860222146583932580700505)
            ·
              refine ⟨645166609937949435525379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 860222146583932580700505 645166609937949435525379)
              ·
                refine ⟨967749914906924153288069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645166609937949435525379 967749914906924153288069)
                ·
                  refine ⟨181453109045048278741513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 967749914906924153288069 181453109045048278741513)
                  ·
                    rfl

theorem cell20_397551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_397551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397551 prefixEnd_397551 := by exact prefixLift 397551
  have htrace : WordTrace (prefixWord ++ tailWord_397551) baseStart_397551 baseEnd_397551 := by
    simpa [prefixWord, tailWord_397551, baseEnd_397551] using wordTrace_append hprefix tailTrace_397551
  have hstable : (prefixWord ++ tailWord_397551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397551).length < 2 ^ (prefixWord ++ tailWord_397551).sum := by decide
  have hdescent : baseEnd_397551 < baseStart_397551 := by decide
  rcases family_descends (prefixWord ++ tailWord_397551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397565 : List Nat := [1, 4, 1, 1, 1, 1, 1, 7, 3]
def baseStart_397565 : Nat := 118140960795 + 397565 * 2 ^ 59
def prefixEnd_397565 : Nat := 4983230072969 + 3 ^ 40 * 397565 * 2
def baseEnd_397565 : Nat := 181459499026526452274789

theorem tailTrace_397565 : CollatzResearch.WordTrace tailWord_397565 prefixEnd_397565 181459499026526452274789 := by
  unfold tailWord_397565
  simp only [CollatzResearch.WordTrace]
  refine ⟨14500386804697378541418149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9666924536464919027612099 14500386804697378541418149)
  ·
    refine ⟨2718822525880758476515903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14500386804697378541418149 2718822525880758476515903)
    ·
      refine ⟨4078233788821137714773855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2718822525880758476515903 4078233788821137714773855)
      ·
        refine ⟨6117350683231706572160783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4078233788821137714773855 6117350683231706572160783)
        ·
          refine ⟨9176026024847559858241175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6117350683231706572160783 9176026024847559858241175)
          ·
            refine ⟨13764039037271339787361763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9176026024847559858241175 13764039037271339787361763)
            ·
              refine ⟨20646058555907009681042645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13764039037271339787361763 20646058555907009681042645)
              ·
                refine ⟨483891997404070539399437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20646058555907009681042645 483891997404070539399437)
                ·
                  refine ⟨181459499026526452274789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483891997404070539399437 181459499026526452274789)
                  ·
                    rfl

theorem cell20_397565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_397565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397565 prefixEnd_397565 := by exact prefixLift 397565
  have htrace : WordTrace (prefixWord ++ tailWord_397565) baseStart_397565 baseEnd_397565 := by
    simpa [prefixWord, tailWord_397565, baseEnd_397565] using wordTrace_append hprefix tailTrace_397565
  have hstable : (prefixWord ++ tailWord_397565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397565).length < 2 ^ (prefixWord ++ tailWord_397565).sum := by decide
  have hdescent : baseEnd_397565 < baseStart_397565 := by decide
  rcases family_descends (prefixWord ++ tailWord_397565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397575 : List Nat := [1, 1, 4, 5, 1, 1, 1, 6]
def baseStart_397575 : Nat := 118140960795 + 397575 * 2 ^ 59
def prefixEnd_397575 : Nat := 4983230072969 + 3 ^ 40 * 397575 * 2
def baseEnd_397575 : Nat := 60488021099670287313805

theorem tailTrace_397575 : CollatzResearch.WordTrace tailWord_397575 prefixEnd_397575 60488021099670287313805 := by
  unfold tailWord_397575
  simp only [CollatzResearch.WordTrace]
  refine ⟨14500751534661150249282179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9667167689774100166188119 14500751534661150249282179)
  ·
    refine ⟨21751127301991725373923269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14500751534661150249282179 21751127301991725373923269)
    ·
      refine ⟨4078336369123448507610613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21751127301991725373923269 4078336369123448507610613)
      ·
        refine ⟨382344034605323297588495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4078336369123448507610613 382344034605323297588495)
        ·
          refine ⟨573516051907984946382743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382344034605323297588495 573516051907984946382743)
          ·
            refine ⟨860274077861977419574115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573516051907984946382743 860274077861977419574115)
            ·
              refine ⟨1290411116792966129361173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860274077861977419574115 1290411116792966129361173)
              ·
                refine ⟨60488021099670287313805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1290411116792966129361173 60488021099670287313805)
                ·
                  rfl

theorem cell20_397575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 6].length) (baseStart_397575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397575 prefixEnd_397575 := by exact prefixLift 397575
  have htrace : WordTrace (prefixWord ++ tailWord_397575) baseStart_397575 baseEnd_397575 := by
    simpa [prefixWord, tailWord_397575, baseEnd_397575] using wordTrace_append hprefix tailTrace_397575
  have hstable : (prefixWord ++ tailWord_397575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397575).length < 2 ^ (prefixWord ++ tailWord_397575).sum := by decide
  have hdescent : baseEnd_397575 < baseStart_397575 := by decide
  rcases family_descends (prefixWord ++ tailWord_397575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397579 : List Nat := [1, 1, 1, 1, 5, 2, 3, 6]
def baseStart_397579 : Nat := 118140960795 + 397579 * 2 ^ 59
def prefixEnd_397579 : Nat := 4983230072969 + 3 ^ 40 * 397579 * 2
def baseEnd_397579 : Nat := 60488629669334875269355

theorem tailTrace_397579 : CollatzResearch.WordTrace tailWord_397579 prefixEnd_397579 60488629669334875269355 := by
  unfold tailWord_397579
  simp only [CollatzResearch.WordTrace]
  refine ⟨14500897426646658932427791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9667264951097772621618527 14500897426646658932427791)
  ·
    refine ⟨21751346139969988398641687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14500897426646658932427791 21751346139969988398641687)
    ·
      refine ⟨32627019209954982597962531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21751346139969988398641687 32627019209954982597962531)
      ·
        refine ⟨48940528814932473896943797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32627019209954982597962531 48940528814932473896943797)
        ·
          refine ⟨4588174576399919427838481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48940528814932473896943797 4588174576399919427838481)
          ·
            refine ⟨3441130932299939570878861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4588174576399919427838481 3441130932299939570878861)
            ·
              refine ⟨1290424099612477339079573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3441130932299939570878861 1290424099612477339079573)
              ·
                refine ⟨60488629669334875269355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1290424099612477339079573 60488629669334875269355)
                ·
                  rfl

theorem cell20_397579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 6].length) (baseStart_397579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397579 prefixEnd_397579 := by exact prefixLift 397579
  have htrace : WordTrace (prefixWord ++ tailWord_397579) baseStart_397579 baseEnd_397579 := by
    simpa [prefixWord, tailWord_397579, baseEnd_397579] using wordTrace_append hprefix tailTrace_397579
  have hstable : (prefixWord ++ tailWord_397579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397579).length < 2 ^ (prefixWord ++ tailWord_397579).sum := by decide
  have hdescent : baseEnd_397579 < baseStart_397579 := by decide
  rcases family_descends (prefixWord ++ tailWord_397579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397603 : List Nat := [1, 1, 1, 4, 2, 2, 2, 4, 3]
def baseStart_397603 : Nat := 118140960795 + 397603 * 2 ^ 59
def prefixEnd_397603 : Nat := 4983230072969 + 3 ^ 40 * 397603 * 2
def baseEnd_397603 : Nat := 181476843261967209007967

theorem tailTrace_397603 : CollatzResearch.WordTrace tailWord_397603 prefixEnd_397603 181476843261967209007967 := by
  unfold tailWord_397603
  simp only [CollatzResearch.WordTrace]
  refine ⟨14501772778559711031301463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9667848519039807354200975 14501772778559711031301463)
  ·
    refine ⟨21752659167839566546952195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14501772778559711031301463 21752659167839566546952195)
    ·
      refine ⟨32628988751759349820428293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21752659167839566546952195 32628988751759349820428293)
      ·
        refine ⟨6117935390954878091330305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32628988751759349820428293 6117935390954878091330305)
        ·
          refine ⟨4588451543216158568497729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6117935390954878091330305 4588451543216158568497729)
          ·
            refine ⟨3441338657412118926373297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4588451543216158568497729 3441338657412118926373297)
            ·
              refine ⟨2581003993059089194779973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3441338657412118926373297 2581003993059089194779973)
              ·
                refine ⟨483938248698579224021245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2581003993059089194779973 483938248698579224021245)
                ·
                  refine ⟨181476843261967209007967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483938248698579224021245 181476843261967209007967)
                  ·
                    rfl

theorem cell20_397603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 3].length) (baseStart_397603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397603 prefixEnd_397603 := by exact prefixLift 397603
  have htrace : WordTrace (prefixWord ++ tailWord_397603) baseStart_397603 baseEnd_397603 := by
    simpa [prefixWord, tailWord_397603, baseEnd_397603] using wordTrace_append hprefix tailTrace_397603
  have hstable : (prefixWord ++ tailWord_397603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397603).length < 2 ^ (prefixWord ++ tailWord_397603).sum := by decide
  have hdescent : baseEnd_397603 < baseStart_397603 := by decide
  rcases family_descends (prefixWord ++ tailWord_397603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397672 : List Nat := [2, 1, 4, 2, 2, 1, 3, 5]
def baseStart_397672 : Nat := 118140960795 + 397672 * 2 ^ 59
def prefixEnd_397672 : Nat := 4983230072969 + 3 ^ 40 * 397672 * 2
def baseEnd_397672 : Nat := 60502778914036545235895

theorem tailTrace_397672 : CollatzResearch.WordTrace tailWord_397672 prefixEnd_397672 60502778914036545235895 := by
  unfold tailWord_397672
  simp only [CollatzResearch.WordTrace]
  refine ⟨7252144707654867907781635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9669526276873157210375513 7252144707654867907781635)
  ·
    refine ⟨10878217061482301861672453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7252144707654867907781635 10878217061482301861672453)
    ·
      refine ⟨2039665699027931599063585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10878217061482301861672453 2039665699027931599063585)
      ·
        refine ⟨1529749274270948699297689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2039665699027931599063585 1529749274270948699297689)
        ·
          refine ⟨1147311955703211524473267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1529749274270948699297689 1147311955703211524473267)
          ·
            refine ⟨1720967933554817286709901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147311955703211524473267 1720967933554817286709901)
            ·
              refine ⟨645362975083056482516213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1720967933554817286709901 645362975083056482516213)
              ·
                refine ⟨60502778914036545235895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 645362975083056482516213 60502778914036545235895)
                ·
                  rfl

theorem cell20_397672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_397672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397672 prefixEnd_397672 := by exact prefixLift 397672
  have htrace : WordTrace (prefixWord ++ tailWord_397672) baseStart_397672 baseEnd_397672 := by
    simpa [prefixWord, tailWord_397672, baseEnd_397672] using wordTrace_append hprefix tailTrace_397672
  have hstable : (prefixWord ++ tailWord_397672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397672).length < 2 ^ (prefixWord ++ tailWord_397672).sum := by decide
  have hdescent : baseEnd_397672 < baseStart_397672 := by decide
  rcases family_descends (prefixWord ++ tailWord_397672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397710 : List Nat := [4, 1, 1, 4, 1, 2, 7]
def baseStart_397710 : Nat := 118140960795 + 397710 * 2 ^ 59
def prefixEnd_397710 : Nat := 4983230072969 + 3 ^ 40 * 397710 * 2
def baseEnd_397710 : Nat := 20169520108616710271207

theorem tailTrace_397710 : CollatzResearch.WordTrace tailWord_397710 prefixEnd_397710 20169520108616710271207 := by
  unfold tailWord_397710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1813209423646508538180823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9670450259448045536964389 1813209423646508538180823)
  ·
    refine ⟨2719814135469762807271235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1813209423646508538180823 2719814135469762807271235)
    ·
      refine ⟨4079721203204644210906853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2719814135469762807271235 4079721203204644210906853)
      ·
        refine ⟨764947725600870789545035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4079721203204644210906853 764947725600870789545035)
        ·
          refine ⟨1147421588401306184317553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764947725600870789545035 1147421588401306184317553)
          ·
            refine ⟨860566191300979638238165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1147421588401306184317553 860566191300979638238165)
            ·
              refine ⟨20169520108616710271207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 860566191300979638238165 20169520108616710271207)
              ·
                rfl

theorem cell20_397710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 7].length) (baseStart_397710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397710 prefixEnd_397710 := by exact prefixLift 397710
  have htrace : WordTrace (prefixWord ++ tailWord_397710) baseStart_397710 baseEnd_397710 := by
    simpa [prefixWord, tailWord_397710, baseEnd_397710] using wordTrace_append hprefix tailTrace_397710
  have hstable : (prefixWord ++ tailWord_397710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397710).length < 2 ^ (prefixWord ++ tailWord_397710).sum := by decide
  have hdescent : baseEnd_397710 < baseStart_397710 := by decide
  rcases family_descends (prefixWord ++ tailWord_397710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397720 : List Nat := [2, 1, 2, 5, 1, 1, 2, 4, 2]
def baseStart_397720 : Nat := 118140960795 + 397720 * 2 ^ 59
def prefixEnd_397720 : Nat := 4983230072969 + 3 ^ 40 * 397720 * 2
def baseEnd_397720 : Nat := 181530245250034802107489

theorem tailTrace_397720 : CollatzResearch.WordTrace tailWord_397720 prefixEnd_397720 181530245250034802107489 := by
  unfold tailWord_397720
  simp only [CollatzResearch.WordTrace]
  refine ⟨7253020059567920006655307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9670693412757226675540409 7253020059567920006655307)
  ·
    refine ⟨10879530089351880009982961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7253020059567920006655307 10879530089351880009982961)
    ·
      refine ⟨8159647567013910007487221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10879530089351880009982961 8159647567013910007487221)
      ·
        refine ⟨764966959407554063201927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8159647567013910007487221 764966959407554063201927)
        ·
          refine ⟨1147450439111331094802891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764966959407554063201927 1147450439111331094802891)
          ·
            refine ⟨1721175658666996642204337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147450439111331094802891 1721175658666996642204337)
            ·
              refine ⟨1290881744000247481653253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1721175658666996642204337 1290881744000247481653253)
              ·
                refine ⟨242040327000046402809985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1290881744000247481653253 242040327000046402809985)
                ·
                  refine ⟨181530245250034802107489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242040327000046402809985 181530245250034802107489)
                  ·
                    rfl

theorem cell20_397720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 2].length) (baseStart_397720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397720 prefixEnd_397720 := by exact prefixLift 397720
  have htrace : WordTrace (prefixWord ++ tailWord_397720) baseStart_397720 baseEnd_397720 := by
    simpa [prefixWord, tailWord_397720, baseEnd_397720] using wordTrace_append hprefix tailTrace_397720
  have hstable : (prefixWord ++ tailWord_397720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397720).length < 2 ^ (prefixWord ++ tailWord_397720).sum := by decide
  have hdescent : baseEnd_397720 < baseStart_397720 := by decide
  rcases family_descends (prefixWord ++ tailWord_397720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397758 : List Nat := [4, 2, 1, 1, 1, 1, 5, 3, 2]
def baseStart_397758 : Nat := 118140960795 + 397758 * 2 ^ 59
def prefixEnd_397758 : Nat := 4983230072969 + 3 ^ 40 * 397758 * 2
def baseEnd_397758 : Nat := 181547589485475558840667

theorem tailTrace_397758 : CollatzResearch.WordTrace tailWord_397758 prefixEnd_397758 181547589485475558840667 := by
  unfold tailWord_397758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1813428261624771562899241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9671617395332115002129285 1813428261624771562899241)
  ·
    refine ⟨1360071196218578672174431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1813428261624771562899241 1360071196218578672174431)
    ·
      refine ⟨2040106794327868008261647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1360071196218578672174431 2040106794327868008261647)
      ·
        refine ⟨3060160191491802012392471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2040106794327868008261647 3060160191491802012392471)
        ·
          refine ⟨4590240287237703018588707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3060160191491802012392471 4590240287237703018588707)
          ·
            refine ⟨6885360430856554527883061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4590240287237703018588707 6885360430856554527883061)
            ·
              refine ⟨645502540392801986989037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6885360430856554527883061 645502540392801986989037)
              ·
                refine ⟨242063452647300745120889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 645502540392801986989037 242063452647300745120889)
                ·
                  refine ⟨181547589485475558840667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242063452647300745120889 181547589485475558840667)
                  ·
                    rfl

theorem cell20_397758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_397758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397758 prefixEnd_397758 := by exact prefixLift 397758
  have htrace : WordTrace (prefixWord ++ tailWord_397758) baseStart_397758 baseEnd_397758 := by
    simpa [prefixWord, tailWord_397758, baseEnd_397758] using wordTrace_append hprefix tailTrace_397758
  have hstable : (prefixWord ++ tailWord_397758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397758).length < 2 ^ (prefixWord ++ tailWord_397758).sum := by decide
  have hdescent : baseEnd_397758 < baseStart_397758 := by decide
  rcases family_descends (prefixWord ++ tailWord_397758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397761 : List Nat := [1, 2, 7, 1, 2, 1, 6]
def baseStart_397761 : Nat := 118140960795 + 397761 * 2 ^ 59
def prefixEnd_397761 : Nat := 4983230072969 + 3 ^ 40 * 397761 * 2
def baseEnd_397761 : Nat := 20172106529691209082295

theorem tailTrace_397761 : CollatzResearch.WordTrace tailWord_397761 prefixEnd_397761 20172106529691209082295 := by
  unfold tailWord_397761
  simp only [CollatzResearch.WordTrace]
  refine ⟨14507535511987304015553137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9671690341324869343702091 14507535511987304015553137)
  ·
    refine ⟨10880651633990478011664853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14507535511987304015553137 10880651633990478011664853)
    ·
      refine ⟨255015272671651828398395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 10880651633990478011664853 255015272671651828398395)
      ·
        refine ⟨382522909007477742597593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255015272671651828398395 382522909007477742597593)
        ·
          refine ⟨286892181755608306948195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382522909007477742597593 286892181755608306948195)
          ·
            refine ⟨430338272633412460422293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286892181755608306948195 430338272633412460422293)
            ·
              refine ⟨20172106529691209082295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 430338272633412460422293 20172106529691209082295)
              ·
                rfl

theorem cell20_397761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 6].length) (baseStart_397761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397761 prefixEnd_397761 := by exact prefixLift 397761
  have htrace : WordTrace (prefixWord ++ tailWord_397761) baseStart_397761 baseEnd_397761 := by
    simpa [prefixWord, tailWord_397761, baseEnd_397761] using wordTrace_append hprefix tailTrace_397761
  have hstable : (prefixWord ++ tailWord_397761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397761).length < 2 ^ (prefixWord ++ tailWord_397761).sum := by decide
  have hdescent : baseEnd_397761 < baseStart_397761 := by decide
  rcases family_descends (prefixWord ++ tailWord_397761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397793 : List Nat := [1, 2, 3, 1, 2, 2, 3, 3, 3]
def baseStart_397793 : Nat := 118140960795 + 397793 * 2 ^ 59
def prefixEnd_397793 : Nat := 4983230072969 + 3 ^ 40 * 397793 * 2
def baseEnd_397793 : Nat := 181563564439170992673857

theorem tailTrace_397793 : CollatzResearch.WordTrace tailWord_397793 prefixEnd_397793 181563564439170992673857 := by
  unfold tailWord_397793
  simp only [CollatzResearch.WordTrace]
  refine ⟨14508702647871373480718033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9672468431914248987145355 14508702647871373480718033)
  ·
    refine ⟨10881526985903530110538525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14508702647871373480718033 10881526985903530110538525)
    ·
      refine ⟨4080572619713823791451947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10881526985903530110538525 4080572619713823791451947)
      ·
        refine ⟨6120858929570735687177921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4080572619713823791451947 6120858929570735687177921)
        ·
          refine ⟨4590644197178051765383441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6120858929570735687177921 4590644197178051765383441)
          ·
            refine ⟨3442983147883538824037581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4590644197178051765383441 3442983147883538824037581)
            ·
              refine ⟨1291118680456327059014093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3442983147883538824037581 1291118680456327059014093)
              ·
                refine ⟨484169505171122647130285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1291118680456327059014093 484169505171122647130285)
                ·
                  refine ⟨181563564439170992673857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484169505171122647130285 181563564439170992673857)
                  ·
                    rfl

theorem cell20_397793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 3].length) (baseStart_397793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397793 prefixEnd_397793 := by exact prefixLift 397793
  have htrace : WordTrace (prefixWord ++ tailWord_397793) baseStart_397793 baseEnd_397793 := by
    simpa [prefixWord, tailWord_397793, baseEnd_397793] using wordTrace_append hprefix tailTrace_397793
  have hstable : (prefixWord ++ tailWord_397793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397793).length < 2 ^ (prefixWord ++ tailWord_397793).sum := by decide
  have hdescent : baseEnd_397793 < baseStart_397793 := by decide
  rcases family_descends (prefixWord ++ tailWord_397793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397893 : List Nat := [1, 3, 1, 1, 1, 5, 2, 4, 2]
def baseStart_397893 : Nat := 118140960795 + 397893 * 2 ^ 59
def prefixEnd_397893 : Nat := 4983230072969 + 3 ^ 40 * 397893 * 2
def baseEnd_397893 : Nat := 181609207164015089340115

theorem tailTrace_397893 : CollatzResearch.WordTrace tailWord_397893 prefixEnd_397893 181609207164015089340115 := by
  unfold tailWord_397893
  simp only [CollatzResearch.WordTrace]
  refine ⟨14512349947509090559358333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9674899965006060372905555 14512349947509090559358333)
  ·
    refine ⟨5442131230315908959759375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14512349947509090559358333 5442131230315908959759375)
    ·
      refine ⟨8163196845473863439639063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5442131230315908959759375 8163196845473863439639063)
      ·
        refine ⟨12244795268210795159458595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8163196845473863439639063 12244795268210795159458595)
        ·
          refine ⟨18367192902316192739187893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12244795268210795159458595 18367192902316192739187893)
          ·
            refine ⟨1721924334592143069298865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18367192902316192739187893 1721924334592143069298865)
            ·
              refine ⟨1291443250944107301974149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1721924334592143069298865 1291443250944107301974149)
              ·
                refine ⟨242145609552020119120153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1291443250944107301974149 242145609552020119120153)
                ·
                  refine ⟨181609207164015089340115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242145609552020119120153 181609207164015089340115)
                  ·
                    rfl

theorem cell20_397893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_397893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397893 prefixEnd_397893 := by exact prefixLift 397893
  have htrace : WordTrace (prefixWord ++ tailWord_397893) baseStart_397893 baseEnd_397893 := by
    simpa [prefixWord, tailWord_397893, baseEnd_397893] using wordTrace_append hprefix tailTrace_397893
  have hstable : (prefixWord ++ tailWord_397893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397893).length < 2 ^ (prefixWord ++ tailWord_397893).sum := by decide
  have hdescent : baseEnd_397893 < baseStart_397893 := by decide
  rcases family_descends (prefixWord ++ tailWord_397893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397921 : List Nat := [1, 2, 3, 1, 1, 5, 1, 6]
def baseStart_397921 : Nat := 118140960795 + 397921 * 2 ^ 59
def prefixEnd_397921 : Nat := 4983230072969 + 3 ^ 40 * 397921 * 2
def baseEnd_397921 : Nat := 60540662375657145468889

theorem tailTrace_397921 : CollatzResearch.WordTrace tailWord_397921 prefixEnd_397921 60540662375657145468889 := by
  unfold tailWord_397921
  simp only [CollatzResearch.WordTrace]
  refine ⟨14513371191407651341377617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9675580794271767560918411 14513371191407651341377617)
  ·
    refine ⟨10885028393555738506033213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14513371191407651341377617 10885028393555738506033213)
    ·
      refine ⟨4081885647583401939762455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10885028393555738506033213 4081885647583401939762455)
      ·
        refine ⟨6122828471375102909643683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4081885647583401939762455 6122828471375102909643683)
        ·
          refine ⟨9184242707062654364465525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6122828471375102909643683 9184242707062654364465525)
          ·
            refine ⟨861022753787123846668643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9184242707062654364465525 861022753787123846668643)
            ·
              refine ⟨1291534130680685770002965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861022753787123846668643 1291534130680685770002965)
              ·
                refine ⟨60540662375657145468889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1291534130680685770002965 60540662375657145468889)
                ·
                  rfl

theorem cell20_397921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 6].length) (baseStart_397921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397921 prefixEnd_397921 := by exact prefixLift 397921
  have htrace : WordTrace (prefixWord ++ tailWord_397921) baseStart_397921 baseEnd_397921 := by
    simpa [prefixWord, tailWord_397921, baseEnd_397921] using wordTrace_append hprefix tailTrace_397921
  have hstable : (prefixWord ++ tailWord_397921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397921).length < 2 ^ (prefixWord ++ tailWord_397921).sum := by decide
  have hdescent : baseEnd_397921 < baseStart_397921 := by decide
  rcases family_descends (prefixWord ++ tailWord_397921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397935 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 6]
def baseStart_397935 : Nat := 118140960795 + 397935 * 2 ^ 59
def prefixEnd_397935 : Nat := 4983230072969 + 3 ^ 40 * 397935 * 2
def baseEnd_397935 : Nat := 181628377108449609939943

theorem tailTrace_397935 : CollatzResearch.WordTrace tailWord_397935 prefixEnd_397935 181628377108449609939943 := by
  unfold tailWord_397935
  simp only [CollatzResearch.WordTrace]
  refine ⟨14513881813356931732387259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9675921208904621154924839 14513881813356931732387259)
  ·
    refine ⟨21770822720035397598580889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14513881813356931732387259 21770822720035397598580889)
    ·
      refine ⟨16328117040026548198935667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21770822720035397598580889 16328117040026548198935667)
      ·
        refine ⟨24492175560039822298403501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16328117040026548198935667 24492175560039822298403501)
        ·
          refine ⟨9184565835014933361901313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24492175560039822298403501 9184565835014933361901313)
          ·
            refine ⟨6888424376261200021425985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9184565835014933361901313 6888424376261200021425985)
            ·
              refine ⟨5166318282195900016069489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6888424376261200021425985 5166318282195900016069489)
              ·
                refine ⟨3874738711646925012052117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5166318282195900016069489 3874738711646925012052117)
                ·
                  refine ⟨181628377108449609939943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3874738711646925012052117 181628377108449609939943)
                  ·
                    rfl

theorem cell20_397935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_397935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397935 prefixEnd_397935 := by exact prefixLift 397935
  have htrace : WordTrace (prefixWord ++ tailWord_397935) baseStart_397935 baseEnd_397935 := by
    simpa [prefixWord, tailWord_397935, baseEnd_397935] using wordTrace_append hprefix tailTrace_397935
  have hstable : (prefixWord ++ tailWord_397935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397935).length < 2 ^ (prefixWord ++ tailWord_397935).sum := by decide
  have hdescent : baseEnd_397935 < baseStart_397935 := by decide
  rcases family_descends (prefixWord ++ tailWord_397935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397938 : List Nat := [3, 2, 1, 2, 4, 2, 6]
def baseStart_397938 : Nat := 118140960795 + 397938 * 2 ^ 59
def prefixEnd_397938 : Nat := 4983230072969 + 3 ^ 40 * 397938 * 2
def baseEnd_397938 : Nat := 20181082932243881426659

theorem tailTrace_397938 : CollatzResearch.WordTrace tailWord_397938 prefixEnd_397938 20181082932243881426659 := by
  unfold tailWord_397938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3628497808086515811186617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9675994154897375496497645 3628497808086515811186617)
  ·
    refine ⟨2721373356064886858389963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3628497808086515811186617 2721373356064886858389963)
    ·
      refine ⟨4082060034097330287584945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2721373356064886858389963 4082060034097330287584945)
      ·
        refine ⟨3061545025572997715688709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4082060034097330287584945 3061545025572997715688709)
        ·
          refine ⟨574039692294937071691633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3061545025572997715688709 574039692294937071691633)
          ·
            refine ⟨430529769221202803768725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574039692294937071691633 430529769221202803768725)
            ·
              refine ⟨20181082932243881426659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 430529769221202803768725 20181082932243881426659)
              ·
                rfl

theorem cell20_397938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 6].length) (baseStart_397938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397938 prefixEnd_397938 := by exact prefixLift 397938
  have htrace : WordTrace (prefixWord ++ tailWord_397938) baseStart_397938 baseEnd_397938 := by
    simpa [prefixWord, tailWord_397938, baseEnd_397938] using wordTrace_append hprefix tailTrace_397938
  have hstable : (prefixWord ++ tailWord_397938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397938).length < 2 ^ (prefixWord ++ tailWord_397938).sum := by decide
  have hdescent : baseEnd_397938 < baseStart_397938 := by decide
  rcases family_descends (prefixWord ++ tailWord_397938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397952 : List Nat := [2, 1, 1, 2, 1, 5, 3, 1, 4]
def baseStart_397952 : Nat := 118140960795 + 397952 * 2 ^ 59
def prefixEnd_397952 : Nat := 4983230072969 + 3 ^ 40 * 397952 * 2
def baseEnd_397952 : Nat := 181636136371673106373207

theorem tailTrace_397952 : CollatzResearch.WordTrace tailWord_397952 prefixEnd_397952 181636136371673106373207 := by
  unfold tailWord_397952
  simp only [CollatzResearch.WordTrace]
  refine ⟨7257250927147671817878055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9676334569530229090504073 7257250927147671817878055)
  ·
    refine ⟨10885876390721507726817083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7257250927147671817878055 10885876390721507726817083)
    ·
      refine ⟨16328814586082261590225625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10885876390721507726817083 16328814586082261590225625)
      ·
        refine ⟨12246610939561696192669219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16328814586082261590225625 12246610939561696192669219)
        ·
          refine ⟨18369916409342544289003829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12246610939561696192669219 18369916409342544289003829)
          ·
            refine ⟨1722179663375863527094109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18369916409342544289003829 1722179663375863527094109)
            ·
              refine ⟨645817373765948822660291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1722179663375863527094109 645817373765948822660291)
              ·
                refine ⟨968726060648923233990437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645817373765948822660291 968726060648923233990437)
                ·
                  refine ⟨181636136371673106373207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 968726060648923233990437 181636136371673106373207)
                  ·
                    rfl

theorem cell20_397952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_397952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397952 prefixEnd_397952 := by exact prefixLift 397952
  have htrace : WordTrace (prefixWord ++ tailWord_397952) baseStart_397952 baseEnd_397952 := by
    simpa [prefixWord, tailWord_397952, baseEnd_397952] using wordTrace_append hprefix tailTrace_397952
  have hstable : (prefixWord ++ tailWord_397952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397952).length < 2 ^ (prefixWord ++ tailWord_397952).sum := by decide
  have hdescent : baseEnd_397952 < baseStart_397952 := by decide
  rcases family_descends (prefixWord ++ tailWord_397952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397954 : List Nat := [3, 4, 3, 1, 1, 2, 2, 1, 3]
def baseStart_397954 : Nat := 118140960795 + 397954 * 2 ^ 59
def prefixEnd_397954 : Nat := 4983230072969 + 3 ^ 40 * 397954 * 2
def baseEnd_397954 : Nat := 181637049226169988306533

theorem tailTrace_397954 : CollatzResearch.WordTrace tailWord_397954 prefixEnd_397954 181637049226169988306533 := by
  unfold tailWord_397954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3628643700072024494332229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9676383200192065318219277 3628643700072024494332229)
  ·
    refine ⟨680370693763504592687293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3628643700072024494332229 680370693763504592687293)
    ·
      refine ⟨255139010161314222257735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 680370693763504592687293 255139010161314222257735)
      ·
        refine ⟨382708515241971333386603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 255139010161314222257735 382708515241971333386603)
        ·
          refine ⟨574062772862957000079905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382708515241971333386603 574062772862957000079905)
          ·
            refine ⟨430547079647217750059929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574062772862957000079905 430547079647217750059929)
            ·
              refine ⟨322910309735413312544947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430547079647217750059929 322910309735413312544947)
              ·
                refine ⟨484365464603119968817421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322910309735413312544947 484365464603119968817421)
                ·
                  refine ⟨181637049226169988306533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484365464603119968817421 181637049226169988306533)
                  ·
                    rfl

theorem cell20_397954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_397954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397954 prefixEnd_397954 := by exact prefixLift 397954
  have htrace : WordTrace (prefixWord ++ tailWord_397954) baseStart_397954 baseEnd_397954 := by
    simpa [prefixWord, tailWord_397954, baseEnd_397954] using wordTrace_append hprefix tailTrace_397954
  have hstable : (prefixWord ++ tailWord_397954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397954).length < 2 ^ (prefixWord ++ tailWord_397954).sum := by decide
  have hdescent : baseEnd_397954 < baseStart_397954 := by decide
  rcases family_descends (prefixWord ++ tailWord_397954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397959 : List Nat := [1, 1, 4, 2, 1, 2, 4, 5]
def baseStart_397959 : Nat := 118140960795 + 397959 * 2 ^ 59
def prefixEnd_397959 : Nat := 4983230072969 + 3 ^ 40 * 397959 * 2
def baseEnd_397959 : Nat := 60546443787470731046615

theorem tailTrace_397959 : CollatzResearch.WordTrace tailWord_397959 prefixEnd_397959 60546443787470731046615 := by
  unfold tailWord_397959
  simp only [CollatzResearch.WordTrace]
  refine ⟨14514757165269983831260931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9676504776846655887507287 14514757165269983831260931)
  ·
    refine ⟨21772135747904975746891397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14514757165269983831260931 21772135747904975746891397)
    ·
      refine ⟨4082275452732182952542137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21772135747904975746891397 4082275452732182952542137)
      ·
        refine ⟨3061706589549137214406603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4082275452732182952542137 3061706589549137214406603)
        ·
          refine ⟨4592559884323705821609905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3061706589549137214406603 4592559884323705821609905)
          ·
            refine ⟨3444419913242779366207429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4592559884323705821609905 3444419913242779366207429)
            ·
              refine ⟨645828733733021131163893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3444419913242779366207429 645828733733021131163893)
              ·
                refine ⟨60546443787470731046615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 645828733733021131163893 60546443787470731046615)
                ·
                  rfl

theorem cell20_397959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 5].length) (baseStart_397959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397959 prefixEnd_397959 := by exact prefixLift 397959
  have htrace : WordTrace (prefixWord ++ tailWord_397959) baseStart_397959 baseEnd_397959 := by
    simpa [prefixWord, tailWord_397959, baseEnd_397959] using wordTrace_append hprefix tailTrace_397959
  have hstable : (prefixWord ++ tailWord_397959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397959).length < 2 ^ (prefixWord ++ tailWord_397959).sum := by decide
  have hdescent : baseEnd_397959 < baseStart_397959 := by decide
  rcases family_descends (prefixWord ++ tailWord_397959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397962 : List Nat := [3, 1, 2, 3, 3, 1, 1, 3, 3]
def baseStart_397962 : Nat := 118140960795 + 397962 * 2 ^ 59
def prefixEnd_397962 : Nat := 4983230072969 + 3 ^ 40 * 397962 * 2
def baseEnd_397962 : Nat := 181640700644157516039833

theorem tailTrace_397962 : CollatzResearch.WordTrace tailWord_397962 prefixEnd_397962 181640700644157516039833 := by
  unfold tailWord_397962
  simp only [CollatzResearch.WordTrace]
  refine ⟨3628716646064778835905035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9676577722839410229080093 3628716646064778835905035)
  ·
    refine ⟨5443074969097168253857553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3628716646064778835905035 5443074969097168253857553)
    ·
      refine ⟨4082306226822876190393165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5443074969097168253857553 4082306226822876190393165)
      ·
        refine ⟨1530864835058578571397437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4082306226822876190393165 1530864835058578571397437)
        ·
          refine ⟨574074313146966964274039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1530864835058578571397437 574074313146966964274039)
          ·
            refine ⟨861111469720450446411059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574074313146966964274039 861111469720450446411059)
            ·
              refine ⟨1291667204580675669616589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861111469720450446411059 1291667204580675669616589)
              ·
                refine ⟨484375201717753376106221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1291667204580675669616589 484375201717753376106221)
                ·
                  refine ⟨181640700644157516039833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484375201717753376106221 181640700644157516039833)
                  ·
                    rfl

theorem cell20_397962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_397962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397962 prefixEnd_397962 := by exact prefixLift 397962
  have htrace : WordTrace (prefixWord ++ tailWord_397962) baseStart_397962 baseEnd_397962 := by
    simpa [prefixWord, tailWord_397962, baseEnd_397962] using wordTrace_append hprefix tailTrace_397962
  have hstable : (prefixWord ++ tailWord_397962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397962).length < 2 ^ (prefixWord ++ tailWord_397962).sum := by decide
  have hdescent : baseEnd_397962 < baseStart_397962 := by decide
  rcases family_descends (prefixWord ++ tailWord_397962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397997 : List Nat := [1, 5, 2, 1, 1, 10]
def baseStart_397997 : Nat := 118140960795 + 397997 * 2 ^ 59
def prefixEnd_397997 : Nat := 4983230072969 + 3 ^ 40 * 397997 * 2
def baseEnd_397997 : Nat := 6728025022142701847149

theorem tailTrace_397997 : CollatzResearch.WordTrace tailWord_397997 prefixEnd_397997 6728025022142701847149 := by
  unfold tailWord_397997
  simp only [CollatzResearch.WordTrace]
  refine ⟨14516143139132316321144245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9677428759421544214096163 14516143139132316321144245)
  ·
    refine ⟨1360888419293654655107273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14516143139132316321144245 1360888419293654655107273)
    ·
      refine ⟨1020666314470240991330455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1360888419293654655107273 1020666314470240991330455)
      ·
        refine ⟨1530999471705361486995683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020666314470240991330455 1530999471705361486995683)
        ·
          refine ⟨2296499207558042230493525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530999471705361486995683 2296499207558042230493525)
          ·
            refine ⟨6728025022142701847149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2296499207558042230493525 6728025022142701847149)
            ·
              rfl

theorem cell20_397997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 10].length) (baseStart_397997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_397997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_397997 prefixEnd_397997 := by exact prefixLift 397997
  have htrace : WordTrace (prefixWord ++ tailWord_397997) baseStart_397997 baseEnd_397997 := by
    simpa [prefixWord, tailWord_397997, baseEnd_397997] using wordTrace_append hprefix tailTrace_397997
  have hstable : (prefixWord ++ tailWord_397997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397997).length < 2 ^ (prefixWord ++ tailWord_397997).sum := by decide
  have hdescent : baseEnd_397997 < baseStart_397997 := by decide
  rcases family_descends (prefixWord ++ tailWord_397997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398028 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 6]
def baseStart_398028 : Nat := 118140960795 + 398028 * 2 ^ 59
def prefixEnd_398028 : Nat := 4983230072969 + 3 ^ 40 * 398028 * 2
def baseEnd_398028 : Nat := 181670824842554619839563

theorem tailTrace_398028 : CollatzResearch.WordTrace tailWord_398028 prefixEnd_398028 181670824842554619839563 := by
  unfold tailWord_398028
  simp only [CollatzResearch.WordTrace]
  refine ⟨7258636901010004307761369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9678182534680005743681825 7258636901010004307761369)
  ·
    refine ⟨5443977675757503230821027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7258636901010004307761369 5443977675757503230821027)
    ·
      refine ⟨8165966513636254846231541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5443977675757503230821027 8165966513636254846231541)
      ·
        refine ⟨765559360653398891834207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8165966513636254846231541 765559360653398891834207)
        ·
          refine ⟨1148339040980098337751311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765559360653398891834207 1148339040980098337751311)
          ·
            refine ⟨1722508561470147506626967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148339040980098337751311 1722508561470147506626967)
            ·
              refine ⟨2583762842205221259940451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722508561470147506626967 2583762842205221259940451)
              ·
                refine ⟨3875644263307831889910677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583762842205221259940451 3875644263307831889910677)
                ·
                  refine ⟨181670824842554619839563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3875644263307831889910677 181670824842554619839563)
                  ·
                    rfl

theorem cell20_398028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_398028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398028 prefixEnd_398028 := by exact prefixLift 398028
  have htrace : WordTrace (prefixWord ++ tailWord_398028) baseStart_398028 baseEnd_398028 := by
    simpa [prefixWord, tailWord_398028, baseEnd_398028] using wordTrace_append hprefix tailTrace_398028
  have hstable : (prefixWord ++ tailWord_398028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398028).length < 2 ^ (prefixWord ++ tailWord_398028).sum := by decide
  have hdescent : baseEnd_398028 < baseStart_398028 := by decide
  rcases family_descends (prefixWord ++ tailWord_398028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398042 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_398042 : Nat := 118140960795 + 398042 * 2 ^ 59
def prefixEnd_398042 : Nat := 4983230072969 + 3 ^ 40 * 398042 * 2
def baseEnd_398042 : Nat := 181677214824032793372839

theorem tailTrace_398042 : CollatzResearch.WordTrace tailWord_398042 prefixEnd_398042 181677214824032793372839 := by
  unfold tailWord_398042
  simp only [CollatzResearch.WordTrace]
  refine ⟨3629446105992322251633095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9678522949312859337688253 3629446105992322251633095)
  ·
    refine ⟨5444169158988483377449643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3629446105992322251633095 5444169158988483377449643)
    ·
      refine ⟨8166253738482725066174465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5444169158988483377449643 8166253738482725066174465)
      ·
        refine ⟨6124690303862043799630849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8166253738482725066174465 6124690303862043799630849)
        ·
          refine ⟨4593517727896532849723137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6124690303862043799630849 4593517727896532849723137)
          ·
            refine ⟨3445138295922399637292353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4593517727896532849723137 3445138295922399637292353)
            ·
              refine ⟨2583853721941799727969265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3445138295922399637292353 2583853721941799727969265)
              ·
                refine ⟨1937890291456349795976949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2583853721941799727969265 1937890291456349795976949)
                ·
                  refine ⟨181677214824032793372839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1937890291456349795976949 181677214824032793372839)
                  ·
                    rfl

theorem cell20_398042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_398042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398042 prefixEnd_398042 := by exact prefixLift 398042
  have htrace : WordTrace (prefixWord ++ tailWord_398042) baseStart_398042 baseEnd_398042 := by
    simpa [prefixWord, tailWord_398042, baseEnd_398042] using wordTrace_append hprefix tailTrace_398042
  have hstable : (prefixWord ++ tailWord_398042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398042).length < 2 ^ (prefixWord ++ tailWord_398042).sum := by decide
  have hdescent : baseEnd_398042 < baseStart_398042 := by decide
  rcases family_descends (prefixWord ++ tailWord_398042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398066 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_398066 : Nat := 118140960795 + 398066 * 2 ^ 59
def prefixEnd_398066 : Nat := 4983230072969 + 3 ^ 40 * 398066 * 2
def baseEnd_398066 : Nat := 181688169077995376572741

theorem tailTrace_398066 : CollatzResearch.WordTrace tailWord_398066 prefixEnd_398066 181688169077995376572741 := by
  unfold tailWord_398066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3629664943970585276351513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9679106517254894070270701 3629664943970585276351513)
  ·
    refine ⟨2722248707977938957263635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3629664943970585276351513 2722248707977938957263635)
    ·
      refine ⟨4083373061966908435895453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2722248707977938957263635 4083373061966908435895453)
      ·
        refine ⟨1531264898237590663460795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4083373061966908435895453 1531264898237590663460795)
        ·
          refine ⟨2296897347356385995191193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531264898237590663460795 2296897347356385995191193)
          ·
            refine ⟨1722673010517289496393395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2296897347356385995191193 1722673010517289496393395)
            ·
              refine ⟨2584009515775934244590093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722673010517289496393395 2584009515775934244590093)
              ·
                refine ⟨969003568415975341721285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2584009515775934244590093 969003568415975341721285)
                ·
                  refine ⟨181688169077995376572741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 969003568415975341721285 181688169077995376572741)
                  ·
                    rfl

theorem cell20_398066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_398066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398066 prefixEnd_398066 := by exact prefixLift 398066
  have htrace : WordTrace (prefixWord ++ tailWord_398066) baseStart_398066 baseEnd_398066 := by
    simpa [prefixWord, tailWord_398066, baseEnd_398066] using wordTrace_append hprefix tailTrace_398066
  have hstable : (prefixWord ++ tailWord_398066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398066).length < 2 ^ (prefixWord ++ tailWord_398066).sum := by decide
  have hdescent : baseEnd_398066 < baseStart_398066 := by decide
  rcases family_descends (prefixWord ++ tailWord_398066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398076 : List Nat := [2, 2, 2, 1, 3, 3, 3, 1, 3]
def baseStart_398076 : Nat := 118140960795 + 398076 * 2 ^ 59
def prefixEnd_398076 : Nat := 4983230072969 + 3 ^ 40 * 398076 * 2
def baseEnd_398076 : Nat := 181692733350479786239367

theorem tailTrace_398076 : CollatzResearch.WordTrace tailWord_398076 prefixEnd_398076 181692733350479786239367 := by
  unfold tailWord_398076
  simp only [CollatzResearch.WordTrace]
  refine ⟨7259512252923056406635041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9679349670564075208846721 7259512252923056406635041)
  ·
    refine ⟨5444634189692292304976281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7259512252923056406635041 5444634189692292304976281)
    ·
      refine ⟨4083475642269219228732211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5444634189692292304976281 4083475642269219228732211)
      ·
        refine ⟨6125213463403828843098317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4083475642269219228732211 6125213463403828843098317)
        ·
          refine ⟨2296955048776435816161869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6125213463403828843098317 2296955048776435816161869)
          ·
            refine ⟨861358143291163431060701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2296955048776435816161869 861358143291163431060701)
            ·
              refine ⟨323009303734186286647763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 861358143291163431060701 323009303734186286647763)
              ·
                refine ⟨484513955601279429971645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323009303734186286647763 484513955601279429971645)
                ·
                  refine ⟨181692733350479786239367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484513955601279429971645 181692733350479786239367)
                  ·
                    rfl

theorem cell20_398076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_398076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398076 prefixEnd_398076 := by exact prefixLift 398076
  have htrace : WordTrace (prefixWord ++ tailWord_398076) baseStart_398076 baseEnd_398076 := by
    simpa [prefixWord, tailWord_398076, baseEnd_398076] using wordTrace_append hprefix tailTrace_398076
  have hstable : (prefixWord ++ tailWord_398076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398076).length < 2 ^ (prefixWord ++ tailWord_398076).sum := by decide
  have hdescent : baseEnd_398076 < baseStart_398076 := by decide
  rcases family_descends (prefixWord ++ tailWord_398076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398111 : List Nat := [1, 1, 2, 4, 2, 4, 6]
def baseStart_398111 : Nat := 118140960795 + 398111 * 2 ^ 59
def prefixEnd_398111 : Nat := 4983230072969 + 3 ^ 40 * 398111 * 2
def baseEnd_398111 : Nat := 20189856478241691119173

theorem tailTrace_398111 : CollatzResearch.WordTrace tailWord_398111 prefixEnd_398111 20189856478241691119173 := by
  unfold tailWord_398111
  simp only [CollatzResearch.WordTrace]
  refine ⟨14520301060719313790794187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9680200707146209193862791 14520301060719313790794187)
  ·
    refine ⟨21780451591078970686191281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14520301060719313790794187 21780451591078970686191281)
    ·
      refine ⟨16335338693309228014643461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21780451591078970686191281 16335338693309228014643461)
      ·
        refine ⟨3062876004995480252745649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16335338693309228014643461 3062876004995480252745649)
        ·
          refine ⟨2297157003746610189559237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3062876004995480252745649 2297157003746610189559237)
          ·
            refine ⟨430716938202489410542357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2297157003746610189559237 430716938202489410542357)
            ·
              refine ⟨20189856478241691119173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 430716938202489410542357 20189856478241691119173)
              ·
                rfl

theorem cell20_398111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 6].length) (baseStart_398111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398111 prefixEnd_398111 := by exact prefixLift 398111
  have htrace : WordTrace (prefixWord ++ tailWord_398111) baseStart_398111 baseEnd_398111 := by
    simpa [prefixWord, tailWord_398111, baseEnd_398111] using wordTrace_append hprefix tailTrace_398111
  have hstable : (prefixWord ++ tailWord_398111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398111).length < 2 ^ (prefixWord ++ tailWord_398111).sum := by decide
  have hdescent : baseEnd_398111 < baseStart_398111 := by decide
  rcases family_descends (prefixWord ++ tailWord_398111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398170 : List Nat := [3, 1, 1, 2, 1, 12]
def baseStart_398170 : Nat := 118140960795 + 398170 * 2 ^ 59
def prefixEnd_398170 : Nat := 4983230072969 + 3 ^ 40 * 398170 * 2
def baseEnd_398170 : Nat := 6730949537475305077987

theorem tailTrace_398170 : CollatzResearch.WordTrace tailWord_398170 prefixEnd_398170 6730949537475305077987 := by
  unfold tailWord_398170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3630613241876391716797991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9681635311670377911461309 3630613241876391716797991)
  ·
    refine ⟨5445919862814587575196987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3630613241876391716797991 5445919862814587575196987)
    ·
      refine ⟨8168879794221881362795481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5445919862814587575196987 8168879794221881362795481)
      ·
        refine ⟨6126659845666411022096611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8168879794221881362795481 6126659845666411022096611)
        ·
          refine ⟨9189989768499616533144917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6126659845666411022096611 9189989768499616533144917)
          ·
            refine ⟨6730949537475305077987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9189989768499616533144917 6730949537475305077987)
            ·
              rfl

theorem cell20_398170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 12].length) (baseStart_398170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398170 prefixEnd_398170 := by exact prefixLift 398170
  have htrace : WordTrace (prefixWord ++ tailWord_398170) baseStart_398170 baseEnd_398170 := by
    simpa [prefixWord, tailWord_398170, baseEnd_398170] using wordTrace_append hprefix tailTrace_398170
  have hstable : (prefixWord ++ tailWord_398170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398170).length < 2 ^ (prefixWord ++ tailWord_398170).sum := by decide
  have hdescent : baseEnd_398170 < baseStart_398170 := by decide
  rcases family_descends (prefixWord ++ tailWord_398170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398201 : List Nat := [1, 2, 1, 3, 2, 3, 1, 1, 6]
def baseStart_398201 : Nat := 118140960795 + 398201 * 2 ^ 59
def prefixEnd_398201 : Nat := 4983230072969 + 3 ^ 40 * 398201 * 2
def baseEnd_398201 : Nat := 181749786756534907072189

theorem tailTrace_398201 : CollatzResearch.WordTrace tailWord_398201 prefixEnd_398201 181749786756534907072189 := by
  unfold tailWord_398201
  simp only [CollatzResearch.WordTrace]
  refine ⟨14523583630393259161570457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9682389086928839441046971 14523583630393259161570457)
  ·
    refine ⟨10892687722794944371177843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14523583630393259161570457 10892687722794944371177843)
    ·
      refine ⟨16339031584192416556766765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10892687722794944371177843 16339031584192416556766765)
      ·
        refine ⟨6127136844072156208787537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16339031584192416556766765 6127136844072156208787537)
        ·
          refine ⟨4595352633054117156590653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6127136844072156208787537 4595352633054117156590653)
          ·
            refine ⟨1723257237395293933721495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4595352633054117156590653 1723257237395293933721495)
            ·
              refine ⟨2584885856092940900582243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723257237395293933721495 2584885856092940900582243)
              ·
                refine ⟨3877328784139411350873365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584885856092940900582243 3877328784139411350873365)
                ·
                  refine ⟨181749786756534907072189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3877328784139411350873365 181749786756534907072189)
                  ·
                    rfl

theorem cell20_398201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_398201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398201 prefixEnd_398201 := by exact prefixLift 398201
  have htrace : WordTrace (prefixWord ++ tailWord_398201) baseStart_398201 baseEnd_398201 := by
    simpa [prefixWord, tailWord_398201, baseEnd_398201] using wordTrace_append hprefix tailTrace_398201
  have hstable : (prefixWord ++ tailWord_398201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398201).length < 2 ^ (prefixWord ++ tailWord_398201).sum := by decide
  have hdescent : baseEnd_398201 < baseStart_398201 := by decide
  rcases family_descends (prefixWord ++ tailWord_398201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398210 : List Nat := [3, 4, 2, 2, 1, 1, 2, 3, 2]
def baseStart_398210 : Nat := 118140960795 + 398210 * 2 ^ 59
def prefixEnd_398210 : Nat := 4983230072969 + 3 ^ 40 * 398210 * 2
def baseEnd_398210 : Nat := 181753894601770875772153

theorem tailTrace_398210 : CollatzResearch.WordTrace tailWord_398210 prefixEnd_398210 181753894601770875772153 := by
  unfold tailWord_398210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3630977971840163424662021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9682607924907102465765389 3630977971840163424662021)
  ·
    refine ⟨680808369720030642124129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3630977971840163424662021 680808369720030642124129)
    ·
      refine ⟨510606277290022981593097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 680808369720030642124129 510606277290022981593097)
      ·
        refine ⟨382954707967517236194823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 510606277290022981593097 382954707967517236194823)
        ·
          refine ⟨574432061951275854292235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382954707967517236194823 574432061951275854292235)
          ·
            refine ⟨861648092926913781438353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574432061951275854292235 861648092926913781438353)
            ·
              refine ⟨646236069695185336078765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861648092926913781438353 646236069695185336078765)
              ·
                refine ⟨242338526135694501029537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 646236069695185336078765 242338526135694501029537)
                ·
                  refine ⟨181753894601770875772153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242338526135694501029537 181753894601770875772153)
                  ·
                    rfl

theorem cell20_398210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_398210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398210 prefixEnd_398210 := by exact prefixLift 398210
  have htrace : WordTrace (prefixWord ++ tailWord_398210) baseStart_398210 baseEnd_398210 := by
    simpa [prefixWord, tailWord_398210, baseEnd_398210] using wordTrace_append hprefix tailTrace_398210
  have hstable : (prefixWord ++ tailWord_398210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398210).length < 2 ^ (prefixWord ++ tailWord_398210).sum := by decide
  have hdescent : baseEnd_398210 < baseStart_398210 := by decide
  rcases family_descends (prefixWord ++ tailWord_398210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398249 : List Nat := [1, 2, 1, 1, 1, 1, 9, 1, 3]
def baseStart_398249 : Nat := 118140960795 + 398249 * 2 ^ 59
def prefixEnd_398249 : Nat := 4983230072969 + 3 ^ 40 * 398249 * 2
def baseEnd_398249 : Nat := 181771695264460073471993

theorem tailTrace_398249 : CollatzResearch.WordTrace tailWord_398249 prefixEnd_398249 181771695264460073471993 := by
  unfold tailWord_398249
  simp only [CollatzResearch.WordTrace]
  refine ⟨14525334334219363359317801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9683556222812908906211867 14525334334219363359317801)
  ·
    refine ⟨10894000750664522519488351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14525334334219363359317801 10894000750664522519488351)
    ·
      refine ⟨16341001125996783779232527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10894000750664522519488351 16341001125996783779232527)
      ·
        refine ⟨24511501688995175668848791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16341001125996783779232527 24511501688995175668848791)
        ·
          refine ⟨36767252533492763503273187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24511501688995175668848791 36767252533492763503273187)
          ·
            refine ⟨55150878800239145254909781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36767252533492763503273187 55150878800239145254909781)
            ·
              refine ⟨323149680470151241727987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 55150878800239145254909781 323149680470151241727987)
              ·
                refine ⟨484724520705226862591981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323149680470151241727987 484724520705226862591981)
                ·
                  refine ⟨181771695264460073471993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484724520705226862591981 181771695264460073471993)
                  ·
                    rfl

theorem cell20_398249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 3].length) (baseStart_398249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398249 prefixEnd_398249 := by exact prefixLift 398249
  have htrace : WordTrace (prefixWord ++ tailWord_398249) baseStart_398249 baseEnd_398249 := by
    simpa [prefixWord, tailWord_398249, baseEnd_398249] using wordTrace_append hprefix tailTrace_398249
  have hstable : (prefixWord ++ tailWord_398249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398249).length < 2 ^ (prefixWord ++ tailWord_398249).sum := by decide
  have hdescent : baseEnd_398249 < baseStart_398249 := by decide
  rcases family_descends (prefixWord ++ tailWord_398249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398263 : List Nat := [1, 1, 3, 1, 3, 1, 6, 4]
def baseStart_398263 : Nat := 118140960795 + 398263 * 2 ^ 59
def prefixEnd_398263 : Nat := 4983230072969 + 3 ^ 40 * 398263 * 2
def baseEnd_398263 : Nat := 60592695081979415668423

theorem tailTrace_398263 : CollatzResearch.WordTrace tailWord_398263 prefixEnd_398263 60592695081979415668423 := by
  unfold tailWord_398263
  simp only [CollatzResearch.WordTrace]
  refine ⟨14525844956168643750327443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9683896637445762500218295 14525844956168643750327443)
  ·
    refine ⟨21788767434252965625491165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14525844956168643750327443 21788767434252965625491165)
    ·
      refine ⟨8170787787844862109559187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21788767434252965625491165 8170787787844862109559187)
      ·
        refine ⟨12256181681767293164338781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8170787787844862109559187 12256181681767293164338781)
        ·
          refine ⟨4596068130662734936627043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12256181681767293164338781 4596068130662734936627043)
          ·
            refine ⟨6894102195994102404940565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4596068130662734936627043 6894102195994102404940565)
            ·
              refine ⟨323161040437223550231589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6894102195994102404940565 323161040437223550231589)
              ·
                refine ⟨60592695081979415668423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323161040437223550231589 60592695081979415668423)
                ·
                  rfl

theorem cell20_398263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 4].length) (baseStart_398263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398263 prefixEnd_398263 := by exact prefixLift 398263
  have htrace : WordTrace (prefixWord ++ tailWord_398263) baseStart_398263 baseEnd_398263 := by
    simpa [prefixWord, tailWord_398263, baseEnd_398263] using wordTrace_append hprefix tailTrace_398263
  have hstable : (prefixWord ++ tailWord_398263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398263).length < 2 ^ (prefixWord ++ tailWord_398263).sum := by decide
  have hdescent : baseEnd_398263 < baseStart_398263 := by decide
  rcases family_descends (prefixWord ++ tailWord_398263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398269 : List Nat := [1, 4, 1, 2, 5, 1, 1, 3, 2]
def baseStart_398269 : Nat := 118140960795 + 398269 * 2 ^ 59
def prefixEnd_398269 : Nat := 4983230072969 + 3 ^ 40 * 398269 * 2
def baseEnd_398269 : Nat := 181780823809428892805245

theorem tailTrace_398269 : CollatzResearch.WordTrace tailWord_398269 prefixEnd_398269 181780823809428892805245 := by
  unfold tailWord_398269
  simp only [CollatzResearch.WordTrace]
  refine ⟨14526063794146906775045861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9684042529431271183363907 14526063794146906775045861)
  ·
    refine ⟨2723636961402545020321099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14526063794146906775045861 2723636961402545020321099)
    ·
      refine ⟨4085455442103817530481649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2723636961402545020321099 4085455442103817530481649)
      ·
        refine ⟨3064091581577863147861237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4085455442103817530481649 3064091581577863147861237)
        ·
          refine ⟨287258585772924670111991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3064091581577863147861237 287258585772924670111991)
          ·
            refine ⟨430887878659387005167987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287258585772924670111991 430887878659387005167987)
            ·
              refine ⟨646331817989080507751981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430887878659387005167987 646331817989080507751981)
              ·
                refine ⟨242374431745905190406993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 646331817989080507751981 242374431745905190406993)
                ·
                  refine ⟨181780823809428892805245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242374431745905190406993 181780823809428892805245)
                  ·
                    rfl

theorem cell20_398269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_398269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398269 prefixEnd_398269 := by exact prefixLift 398269
  have htrace : WordTrace (prefixWord ++ tailWord_398269) baseStart_398269 baseEnd_398269 := by
    simpa [prefixWord, tailWord_398269, baseEnd_398269] using wordTrace_append hprefix tailTrace_398269
  have hstable : (prefixWord ++ tailWord_398269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398269).length < 2 ^ (prefixWord ++ tailWord_398269).sum := by decide
  have hdescent : baseEnd_398269 < baseStart_398269 := by decide
  rcases family_descends (prefixWord ++ tailWord_398269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398270 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_398270 : Nat := 118140960795 + 398270 * 2 ^ 59
def prefixEnd_398270 : Nat := 4983230072969 + 3 ^ 40 * 398270 * 2
def baseEnd_398270 : Nat := 181781280236677333771907

theorem tailTrace_398270 : CollatzResearch.WordTrace tailWord_398270 prefixEnd_398270 181781280236677333771907 := by
  unfold tailWord_398270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1815762533392910493229033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9684066844762189297221509 1815762533392910493229033)
  ·
    refine ⟨1361821900044682869921775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1815762533392910493229033 1361821900044682869921775)
    ·
      refine ⟨2042732850067024304882663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1361821900044682869921775 2042732850067024304882663)
      ·
        refine ⟨3064099275100536457323995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2042732850067024304882663 3064099275100536457323995)
        ·
          refine ⟨4596148912650804685985993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3064099275100536457323995 4596148912650804685985993)
          ·
            refine ⟨3447111684488103514489495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4596148912650804685985993 3447111684488103514489495)
            ·
              refine ⟨5170667526732155271734243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447111684488103514489495 5170667526732155271734243)
              ·
                refine ⟨7756001290098232907601365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5170667526732155271734243 7756001290098232907601365)
                ·
                  refine ⟨181781280236677333771907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7756001290098232907601365 181781280236677333771907)
                  ·
                    rfl

theorem cell20_398270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_398270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398270 prefixEnd_398270 := by exact prefixLift 398270
  have htrace : WordTrace (prefixWord ++ tailWord_398270) baseStart_398270 baseEnd_398270 := by
    simpa [prefixWord, tailWord_398270, baseEnd_398270] using wordTrace_append hprefix tailTrace_398270
  have hstable : (prefixWord ++ tailWord_398270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398270).length < 2 ^ (prefixWord ++ tailWord_398270).sum := by decide
  have hdescent : baseEnd_398270 < baseStart_398270 := by decide
  rcases family_descends (prefixWord ++ tailWord_398270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398280 : List Nat := [2, 1, 3, 1, 6, 1, 6]
def baseStart_398280 : Nat := 118140960795 + 398280 * 2 ^ 59
def prefixEnd_398280 : Nat := 4983230072969 + 3 ^ 40 * 398280 * 2
def baseEnd_398280 : Nat := 20198427167684638159837

theorem tailTrace_398280 : CollatzResearch.WordTrace tailWord_398280 prefixEnd_398280 20198427167684638159837 := by
  unfold tailWord_398280
  simp only [CollatzResearch.WordTrace]
  refine ⟨7263232498553527826848147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9684309998071370435797529 7263232498553527826848147)
  ·
    refine ⟨10894848747830291740272221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7263232498553527826848147 10894848747830291740272221)
    ·
      refine ⟨4085568280436359402602083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10894848747830291740272221 4085568280436359402602083)
      ·
        refine ⟨6128352420654539103903125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4085568280436359402602083 6128352420654539103903125)
        ·
          refine ⟨287266519718181520495459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6128352420654539103903125 287266519718181520495459)
          ·
            refine ⟨430899779577272280743189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287266519718181520495459 430899779577272280743189)
            ·
              refine ⟨20198427167684638159837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 430899779577272280743189 20198427167684638159837)
              ·
                rfl

theorem cell20_398280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 6].length) (baseStart_398280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398280 prefixEnd_398280 := by exact prefixLift 398280
  have htrace : WordTrace (prefixWord ++ tailWord_398280) baseStart_398280 baseEnd_398280 := by
    simpa [prefixWord, tailWord_398280, baseEnd_398280] using wordTrace_append hprefix tailTrace_398280
  have hstable : (prefixWord ++ tailWord_398280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398280).length < 2 ^ (prefixWord ++ tailWord_398280).sum := by decide
  have hdescent : baseEnd_398280 < baseStart_398280 := by decide
  rcases family_descends (prefixWord ++ tailWord_398280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398301 : List Nat := [1, 4, 3, 1, 2, 1, 1, 7]
def baseStart_398301 : Nat := 118140960795 + 398301 * 2 ^ 59
def prefixEnd_398301 : Nat := 4983230072969 + 3 ^ 40 * 398301 * 2
def baseEnd_398301 : Nat := 60598476493793001246149

theorem tailTrace_398301 : CollatzResearch.WordTrace tailWord_398301 prefixEnd_398301 60598476493793001246149 := by
  unfold tailWord_398301
  simp only [CollatzResearch.WordTrace]
  refine ⟨14527230930030976240210757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9684820620020650826807171 14527230930030976240210757)
  ·
    refine ⟨2723855799380808045039517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14527230930030976240210757 2723855799380808045039517)
    ·
      refine ⟨1021445924767803016889819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2723855799380808045039517 1021445924767803016889819)
      ·
        refine ⟨1532168887151704525334729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021445924767803016889819 1532168887151704525334729)
        ·
          refine ⟨1149126665363778394001047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1532168887151704525334729 1149126665363778394001047)
          ·
            refine ⟨1723689998045667591001571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149126665363778394001047 1723689998045667591001571)
            ·
              refine ⟨2585534997068501386502357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723689998045667591001571 2585534997068501386502357)
              ·
                refine ⟨60598476493793001246149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2585534997068501386502357 60598476493793001246149)
                ·
                  rfl

theorem cell20_398301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 7].length) (baseStart_398301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398301 prefixEnd_398301 := by exact prefixLift 398301
  have htrace : WordTrace (prefixWord ++ tailWord_398301) baseStart_398301 baseEnd_398301 := by
    simpa [prefixWord, tailWord_398301, baseEnd_398301] using wordTrace_append hprefix tailTrace_398301
  have hstable : (prefixWord ++ tailWord_398301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398301).length < 2 ^ (prefixWord ++ tailWord_398301).sum := by decide
  have hdescent : baseEnd_398301 < baseStart_398301 := by decide
  rcases family_descends (prefixWord ++ tailWord_398301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398370 : List Nat := [3, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_398370 : Nat := 118140960795 + 398370 * 2 ^ 59
def prefixEnd_398370 : Nat := 4983230072969 + 3 ^ 40 * 398370 * 2
def baseEnd_398370 : Nat := 181826922961521430438165

theorem tailTrace_398370 : CollatzResearch.WordTrace tailWord_398370 prefixEnd_398370 181826922961521430438165 := by
  unfold tailWord_398370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632436891695250256118141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9686498377854000682981709 3632436891695250256118141)
  ·
    refine ⟨1362163834385718846044303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3632436891695250256118141 1362163834385718846044303)
    ·
      refine ⟨2043245751578578269066455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1362163834385718846044303 2043245751578578269066455)
      ·
        refine ⟨3064868627367867403599683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2043245751578578269066455 3064868627367867403599683)
        ·
          refine ⟨4597302941051801105399525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3064868627367867403599683 4597302941051801105399525)
          ·
            refine ⟨861994301447212707262411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4597302941051801105399525 861994301447212707262411)
            ·
              refine ⟨1292991452170819060893617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861994301447212707262411 1292991452170819060893617)
              ·
                refine ⟨969743589128114295670213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1292991452170819060893617 969743589128114295670213)
                ·
                  refine ⟨181826922961521430438165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 969743589128114295670213 181826922961521430438165)
                  ·
                    rfl

theorem cell20_398370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_398370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398370 prefixEnd_398370 := by exact prefixLift 398370
  have htrace : WordTrace (prefixWord ++ tailWord_398370) baseStart_398370 baseEnd_398370 := by
    simpa [prefixWord, tailWord_398370, baseEnd_398370] using wordTrace_append hprefix tailTrace_398370
  have hstable : (prefixWord ++ tailWord_398370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398370).length < 2 ^ (prefixWord ++ tailWord_398370).sum := by decide
  have hdescent : baseEnd_398370 < baseStart_398370 := by decide
  rcases family_descends (prefixWord ++ tailWord_398370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398401 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 5]
def baseStart_398401 : Nat := 118140960795 + 398401 * 2 ^ 59
def prefixEnd_398401 : Nat := 4983230072969 + 3 ^ 40 * 398401 * 2
def baseEnd_398401 : Nat := 181841072206223100404705

theorem tailTrace_398401 : CollatzResearch.WordTrace tailWord_398401 prefixEnd_398401 181841072206223100404705 := by
  unfold tailWord_398401
  simp only [CollatzResearch.WordTrace]
  refine ⟨14530878229668693318851057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9687252153112462212567371 14530878229668693318851057)
  ·
    refine ⟨10898158672251519989138293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14530878229668693318851057 10898158672251519989138293)
    ·
      refine ⟨1021702375523579998981715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10898158672251519989138293 1021702375523579998981715)
      ·
        refine ⟨1532553563285369998472573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021702375523579998981715 1532553563285369998472573)
        ·
          refine ⟨574707586232013749427215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1532553563285369998472573 574707586232013749427215)
          ·
            refine ⟨862061379348020624140823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574707586232013749427215 862061379348020624140823)
            ·
              refine ⟨1293092069022030936211235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862061379348020624140823 1293092069022030936211235)
              ·
                refine ⟨1939638103533046404316853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293092069022030936211235 1939638103533046404316853)
                ·
                  refine ⟨181841072206223100404705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1939638103533046404316853 181841072206223100404705)
                  ·
                    rfl

theorem cell20_398401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_398401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398401 prefixEnd_398401 := by exact prefixLift 398401
  have htrace : WordTrace (prefixWord ++ tailWord_398401) baseStart_398401 baseEnd_398401 := by
    simpa [prefixWord, tailWord_398401, baseEnd_398401] using wordTrace_append hprefix tailTrace_398401
  have hstable : (prefixWord ++ tailWord_398401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398401).length < 2 ^ (prefixWord ++ tailWord_398401).sum := by decide
  have hdescent : baseEnd_398401 < baseStart_398401 := by decide
  rcases family_descends (prefixWord ++ tailWord_398401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398408 : List Nat := [2, 1, 3, 1, 1, 1, 3, 6, 2]
def baseStart_398408 : Nat := 118140960795 + 398408 * 2 ^ 59
def prefixEnd_398408 : Nat := 4983230072969 + 3 ^ 40 * 398408 * 2
def baseEnd_398408 : Nat := 181844267196962187171343

theorem tailTrace_398408 : CollatzResearch.WordTrace tailWord_398408 prefixEnd_398408 181844267196962187171343 := by
  unfold tailWord_398408
  simp only [CollatzResearch.WordTrace]
  refine ⟨7265566770321666757177939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9687422360428889009570585 7265566770321666757177939)
  ·
    refine ⟨10898350155482500135766909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7265566770321666757177939 10898350155482500135766909)
    ·
      refine ⟨4086881308305937550912591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10898350155482500135766909 4086881308305937550912591)
      ·
        refine ⟨6130321962458906326368887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4086881308305937550912591 6130321962458906326368887)
        ·
          refine ⟨9195482943688359489553331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6130321962458906326368887 9195482943688359489553331)
          ·
            refine ⟨13793224415532539234329997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9195482943688359489553331 13793224415532539234329997)
            ·
              refine ⟨5172459155824702212873749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13793224415532539234329997 5172459155824702212873749)
              ·
                refine ⟨242459022929282916228457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5172459155824702212873749 242459022929282916228457)
                ·
                  refine ⟨181844267196962187171343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242459022929282916228457 181844267196962187171343)
                  ·
                    rfl

theorem cell20_398408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 2].length) (baseStart_398408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398408 prefixEnd_398408 := by exact prefixLift 398408
  have htrace : WordTrace (prefixWord ++ tailWord_398408) baseStart_398408 baseEnd_398408 := by
    simpa [prefixWord, tailWord_398408, baseEnd_398408] using wordTrace_append hprefix tailTrace_398408
  have hstable : (prefixWord ++ tailWord_398408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398408).length < 2 ^ (prefixWord ++ tailWord_398408).sum := by decide
  have hdescent : baseEnd_398408 < baseStart_398408 := by decide
  rcases family_descends (prefixWord ++ tailWord_398408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398418 : List Nat := [3, 2, 2, 1, 3, 2, 3, 1, 3]
def baseStart_398418 : Nat := 118140960795 + 398418 * 2 ^ 59
def prefixEnd_398418 : Nat := 4983230072969 + 3 ^ 40 * 398418 * 2
def baseEnd_398418 : Nat := 181848831469446596837969

theorem tailTrace_398418 : CollatzResearch.WordTrace tailWord_398418 prefixEnd_398418 181848831469446596837969 := by
  unfold tailWord_398418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632874567651776305554977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9687665513738070148146605 3632874567651776305554977)
  ·
    refine ⟨2724655925738832229166233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3632874567651776305554977 2724655925738832229166233)
    ·
      refine ⟨2043491944304124171874675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2724655925738832229166233 2043491944304124171874675)
      ·
        refine ⟨3065237916456186257812013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2043491944304124171874675 3065237916456186257812013)
        ·
          refine ⟨1149464218671069846679505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3065237916456186257812013 1149464218671069846679505)
          ·
            refine ⟨862098164003302385009629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1149464218671069846679505 862098164003302385009629)
            ·
              refine ⟨323286811501238394378611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 862098164003302385009629 323286811501238394378611)
              ·
                refine ⟨484930217251857591567917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323286811501238394378611 484930217251857591567917)
                ·
                  refine ⟨181848831469446596837969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484930217251857591567917 181848831469446596837969)
                  ·
                    rfl

theorem cell20_398418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_398418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398418 prefixEnd_398418 := by exact prefixLift 398418
  have htrace : WordTrace (prefixWord ++ tailWord_398418) baseStart_398418 baseEnd_398418 := by
    simpa [prefixWord, tailWord_398418, baseEnd_398418] using wordTrace_append hprefix tailTrace_398418
  have hstable : (prefixWord ++ tailWord_398418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398418).length < 2 ^ (prefixWord ++ tailWord_398418).sum := by decide
  have hdescent : baseEnd_398418 < baseStart_398418 := by decide
  rcases family_descends (prefixWord ++ tailWord_398418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398442 : List Nat := [3, 1, 3, 2, 2, 3, 1, 3, 2]
def baseStart_398442 : Nat := 118140960795 + 398442 * 2 ^ 59
def prefixEnd_398442 : Nat := 4983230072969 + 3 ^ 40 * 398442 * 2
def baseEnd_398442 : Nat := 181859785723409180037871

theorem tailTrace_398442 : CollatzResearch.WordTrace tailWord_398442 prefixEnd_398442 181859785723409180037871 := by
  unfold tailWord_398442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3633093405630039330273395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9688249081680104880729053 3633093405630039330273395)
  ·
    refine ⟨5449640108445058995410093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3633093405630039330273395 5449640108445058995410093)
    ·
      refine ⟨2043615040666897123278785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5449640108445058995410093 2043615040666897123278785)
      ·
        refine ⟨1532711280500172842459089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2043615040666897123278785 1532711280500172842459089)
        ·
          refine ⟨1149533460375129631844317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1532711280500172842459089 1149533460375129631844317)
          ·
            refine ⟨431075047640673611941619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1149533460375129631844317 431075047640673611941619)
            ·
              refine ⟨646612571461010417912429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431075047640673611941619 646612571461010417912429)
              ·
                refine ⟨242479714297878906717161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 646612571461010417912429 242479714297878906717161)
                ·
                  refine ⟨181859785723409180037871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242479714297878906717161 181859785723409180037871)
                  ·
                    rfl

theorem cell20_398442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_398442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398442 prefixEnd_398442 := by exact prefixLift 398442
  have htrace : WordTrace (prefixWord ++ tailWord_398442) baseStart_398442 baseEnd_398442 := by
    simpa [prefixWord, tailWord_398442, baseEnd_398442] using wordTrace_append hprefix tailTrace_398442
  have hstable : (prefixWord ++ tailWord_398442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398442).length < 2 ^ (prefixWord ++ tailWord_398442).sum := by decide
  have hdescent : baseEnd_398442 < baseStart_398442 := by decide
  rcases family_descends (prefixWord ++ tailWord_398442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398460 : List Nat := [2, 2, 2, 1, 1, 3, 2, 4, 3]
def baseStart_398460 : Nat := 118140960795 + 398460 * 2 ^ 59
def prefixEnd_398460 : Nat := 4983230072969 + 3 ^ 40 * 398460 * 2
def baseEnd_398460 : Nat := 181868001413881117437797

theorem tailTrace_398460 : CollatzResearch.WordTrace tailWord_398460 prefixEnd_398460 181868001413881117437797 := by
  unfold tailWord_398460
  simp only [CollatzResearch.WordTrace]
  refine ⟨7266515068227473197624417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9688686757636630930165889 7266515068227473197624417)
  ·
    refine ⟨5449886301170604898218313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7266515068227473197624417 5449886301170604898218313)
    ·
      refine ⟨4087414725877953673663735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5449886301170604898218313 4087414725877953673663735)
      ·
        refine ⟨6131122088816930510495603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4087414725877953673663735 6131122088816930510495603)
        ·
          refine ⟨9196683133225395765743405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6131122088816930510495603 9196683133225395765743405)
          ·
            refine ⟨3448756174959523412153777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9196683133225395765743405 3448756174959523412153777)
            ·
              refine ⟨2586567131219642559115333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3448756174959523412153777 2586567131219642559115333)
              ·
                refine ⟨484981337103682979834125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2586567131219642559115333 484981337103682979834125)
                ·
                  refine ⟨181868001413881117437797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484981337103682979834125 181868001413881117437797)
                  ·
                    rfl

theorem cell20_398460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_398460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398460 prefixEnd_398460 := by exact prefixLift 398460
  have htrace : WordTrace (prefixWord ++ tailWord_398460) baseStart_398460 baseEnd_398460 := by
    simpa [prefixWord, tailWord_398460, baseEnd_398460] using wordTrace_append hprefix tailTrace_398460
  have hstable : (prefixWord ++ tailWord_398460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398460).length < 2 ^ (prefixWord ++ tailWord_398460).sum := by decide
  have hdescent : baseEnd_398460 < baseStart_398460 := by decide
  rcases family_descends (prefixWord ++ tailWord_398460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398536 : List Nat := [2, 1, 3, 1, 2, 1, 4, 3, 3]
def baseStart_398536 : Nat := 118140960795 + 398536 * 2 ^ 59
def prefixEnd_398536 : Nat := 4983230072969 + 3 ^ 40 * 398536 * 2
def baseEnd_398536 : Nat := 181902689884762630904153

theorem tailTrace_398536 : CollatzResearch.WordTrace tailWord_398536 prefixEnd_398536 181902689884762630904153 := by
  unfold tailWord_398536
  simp only [CollatzResearch.WordTrace]
  refine ⟨7267901042089805687507731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9690534722786407583343641 7267901042089805687507731)
  ·
    refine ⟨10901851563134708531261597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7267901042089805687507731 10901851563134708531261597)
    ·
      refine ⟨4088194336175515699223099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10901851563134708531261597 4088194336175515699223099)
      ·
        refine ⟨6132291504263273548834649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4088194336175515699223099 6132291504263273548834649)
        ·
          refine ⟨4599218628197455161625987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6132291504263273548834649 4599218628197455161625987)
          ·
            refine ⟨6898827942296182742438981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4599218628197455161625987 6898827942296182742438981)
            ·
              refine ⟨1293530239180534264207309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6898827942296182742438981 1293530239180534264207309)
              ·
                refine ⟨485073839692700349077741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1293530239180534264207309 485073839692700349077741)
                ·
                  refine ⟨181902689884762630904153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485073839692700349077741 181902689884762630904153)
                  ·
                    rfl

theorem cell20_398536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_398536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398536 prefixEnd_398536 := by exact prefixLift 398536
  have htrace : WordTrace (prefixWord ++ tailWord_398536) baseStart_398536 baseEnd_398536 := by
    simpa [prefixWord, tailWord_398536, baseEnd_398536] using wordTrace_append hprefix tailTrace_398536
  have hstable : (prefixWord ++ tailWord_398536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398536).length < 2 ^ (prefixWord ++ tailWord_398536).sum := by decide
  have hdescent : baseEnd_398536 < baseStart_398536 := by decide
  rcases family_descends (prefixWord ++ tailWord_398536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398560 : List Nat := [2, 1, 1, 3, 1, 4, 1, 5, 2]
def baseStart_398560 : Nat := 118140960795 + 398560 * 2 ^ 59
def prefixEnd_398560 : Nat := 4983230072969 + 3 ^ 40 * 398560 * 2
def baseEnd_398560 : Nat := 181913644138725214104055

theorem tailTrace_398560 : CollatzResearch.WordTrace tailWord_398560 prefixEnd_398560 181913644138725214104055 := by
  unfold tailWord_398560
  simp only [CollatzResearch.WordTrace]
  refine ⟨7268338718046331736944567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9691118290728442315926089 7268338718046331736944567)
  ·
    refine ⟨10902508077069497605416851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7268338718046331736944567 10902508077069497605416851)
    ·
      refine ⟨16353762115604246408125277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10902508077069497605416851 16353762115604246408125277)
      ·
        refine ⟨6132660793351592403046979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16353762115604246408125277 6132660793351592403046979)
        ·
          refine ⟨9198991190027388604570469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6132660793351592403046979 9198991190027388604570469)
          ·
            refine ⟨1724810848130135363356963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9198991190027388604570469 1724810848130135363356963)
            ·
              refine ⟨2587216272195203045035445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724810848130135363356963 2587216272195203045035445)
              ·
                refine ⟨242551525518300285472073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2587216272195203045035445 242551525518300285472073)
                ·
                  refine ⟨181913644138725214104055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242551525518300285472073 181913644138725214104055)
                  ·
                    rfl

theorem cell20_398560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 2].length) (baseStart_398560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398560 prefixEnd_398560 := by exact prefixLift 398560
  have htrace : WordTrace (prefixWord ++ tailWord_398560) baseStart_398560 baseEnd_398560 := by
    simpa [prefixWord, tailWord_398560, baseEnd_398560] using wordTrace_append hprefix tailTrace_398560
  have hstable : (prefixWord ++ tailWord_398560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398560).length < 2 ^ (prefixWord ++ tailWord_398560).sum := by decide
  have hdescent : baseEnd_398560 < baseStart_398560 := by decide
  rcases family_descends (prefixWord ++ tailWord_398560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398567 : List Nat := [1, 1, 5, 3, 2, 1, 7]
def baseStart_398567 : Nat := 118140960795 + 398567 * 2 ^ 59
def prefixEnd_398567 : Nat := 4983230072969 + 3 ^ 40 * 398567 * 2
def baseEnd_398567 : Nat := 20212982125496033430077

theorem tailTrace_398567 : CollatzResearch.WordTrace tailWord_398567 prefixEnd_398567 20212982125496033430077 := by
  unfold tailWord_398567
  simp only [CollatzResearch.WordTrace]
  refine ⟨14536932747067303669393955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9691288498044869112929303 14536932747067303669393955)
  ·
    refine ⟨21805399120600955504090933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14536932747067303669393955 21805399120600955504090933)
    ·
      refine ⟨2044256167556339578508525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21805399120600955504090933 2044256167556339578508525)
      ·
        refine ⟨766596062833627341940697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2044256167556339578508525 766596062833627341940697)
        ·
          refine ⟨574947047125220506455523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 766596062833627341940697 574947047125220506455523)
          ·
            refine ⟨862420570687830759683285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574947047125220506455523 862420570687830759683285)
            ·
              refine ⟨20212982125496033430077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 862420570687830759683285 20212982125496033430077)
              ·
                rfl

theorem cell20_398567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 7].length) (baseStart_398567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398567 prefixEnd_398567 := by exact prefixLift 398567
  have htrace : WordTrace (prefixWord ++ tailWord_398567) baseStart_398567 baseEnd_398567 := by
    simpa [prefixWord, tailWord_398567, baseEnd_398567] using wordTrace_append hprefix tailTrace_398567
  have hstable : (prefixWord ++ tailWord_398567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398567).length < 2 ^ (prefixWord ++ tailWord_398567).sum := by decide
  have hdescent : baseEnd_398567 < baseStart_398567 := by decide
  rcases family_descends (prefixWord ++ tailWord_398567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398591 : List Nat := [1, 1, 2, 2, 1, 6, 3, 1, 3]
def baseStart_398591 : Nat := 118140960795 + 398591 * 2 ^ 59
def prefixEnd_398591 : Nat := 4983230072969 + 3 ^ 40 * 398591 * 2
def baseEnd_398591 : Nat := 181927793383426884070595

theorem tailTrace_398591 : CollatzResearch.WordTrace tailWord_398591 prefixEnd_398591 181927793383426884070595 := by
  unfold tailWord_398591
  simp only [CollatzResearch.WordTrace]
  refine ⟨14537808098980355768267627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9691872065986903845511751 14537808098980355768267627)
  ·
    refine ⟨21806712148470533652401441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14537808098980355768267627 21806712148470533652401441)
    ·
      refine ⟨16355034111352900239301081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21806712148470533652401441 16355034111352900239301081)
      ·
        refine ⟨12266275583514675179475811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16355034111352900239301081 12266275583514675179475811)
        ·
          refine ⟨18399413375272012769213717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12266275583514675179475811 18399413375272012769213717)
          ·
            refine ⟨862472501965875598556893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18399413375272012769213717 862472501965875598556893)
            ·
              refine ⟨323427188237203349458835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 862472501965875598556893 323427188237203349458835)
              ·
                refine ⟨485140782355805024188253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323427188237203349458835 485140782355805024188253)
                ·
                  refine ⟨181927793383426884070595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485140782355805024188253 181927793383426884070595)
                  ·
                    rfl

theorem cell20_398591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 3].length) (baseStart_398591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398591 prefixEnd_398591 := by exact prefixLift 398591
  have htrace : WordTrace (prefixWord ++ tailWord_398591) baseStart_398591 baseEnd_398591 := by
    simpa [prefixWord, tailWord_398591, baseEnd_398591] using wordTrace_append hprefix tailTrace_398591
  have hstable : (prefixWord ++ tailWord_398591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398591).length < 2 ^ (prefixWord ++ tailWord_398591).sum := by decide
  have hdescent : baseEnd_398591 < baseStart_398591 := by decide
  rcases family_descends (prefixWord ++ tailWord_398591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398632 : List Nat := [2, 1, 5, 1, 2, 2, 3, 2, 2]
def baseStart_398632 : Nat := 118140960795 + 398632 * 2 ^ 59
def prefixEnd_398632 : Nat := 4983230072969 + 3 ^ 40 * 398632 * 2
def baseEnd_398632 : Nat := 181946506900612963703761

theorem tailTrace_398632 : CollatzResearch.WordTrace tailWord_398632 prefixEnd_398632 181946506900612963703761 := by
  unfold tailWord_398632
  simp only [CollatzResearch.WordTrace]
  refine ⟨7269651745915909885255075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9692868994554546513673433 7269651745915909885255075)
  ·
    refine ⟨10904477618873864827882613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7269651745915909885255075 10904477618873864827882613)
    ·
      refine ⟨1022294776769424827613995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10904477618873864827882613 1022294776769424827613995)
      ·
        refine ⟨1533442165154137241420993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022294776769424827613995 1533442165154137241420993)
        ·
          refine ⟨1150081623865602931065745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1533442165154137241420993 1150081623865602931065745)
          ·
            refine ⟨862561217899202198299309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1150081623865602931065745 862561217899202198299309)
            ·
              refine ⟨323460456712200824362241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 862561217899202198299309 323460456712200824362241)
              ·
                refine ⟨242595342534150618271681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323460456712200824362241 242595342534150618271681)
                ·
                  refine ⟨181946506900612963703761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242595342534150618271681 181946506900612963703761)
                  ·
                    rfl

theorem cell20_398632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 2].length) (baseStart_398632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398632 prefixEnd_398632 := by exact prefixLift 398632
  have htrace : WordTrace (prefixWord ++ tailWord_398632) baseStart_398632 baseEnd_398632 := by
    simpa [prefixWord, tailWord_398632, baseEnd_398632] using wordTrace_append hprefix tailTrace_398632
  have hstable : (prefixWord ++ tailWord_398632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398632).length < 2 ^ (prefixWord ++ tailWord_398632).sum := by decide
  have hdescent : baseEnd_398632 < baseStart_398632 := by decide
  rcases family_descends (prefixWord ++ tailWord_398632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398650 : List Nat := [3, 1, 1, 1, 4, 1, 3, 3, 3]
def baseStart_398650 : Nat := 118140960795 + 398650 * 2 ^ 59
def prefixEnd_398650 : Nat := 4983230072969 + 3 ^ 40 * 398650 * 2
def baseEnd_398650 : Nat := 181954722591084901103687

theorem tailTrace_398650 : CollatzResearch.WordTrace tailWord_398650 prefixEnd_398650 181954722591084901103687 := by
  unfold tailWord_398650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3634990001441652211166351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9693306670511072563110269 3634990001441652211166351)
  ·
    refine ⟨5452485002162478316749527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3634990001441652211166351 5452485002162478316749527)
    ·
      refine ⟨8178727503243717475124291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5452485002162478316749527 8178727503243717475124291)
      ·
        refine ⟨12268091254865576212686437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8178727503243717475124291 12268091254865576212686437)
        ·
          refine ⟨2300267110287295539878707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12268091254865576212686437 2300267110287295539878707)
          ·
            refine ⟨3450400665430943309818061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300267110287295539878707 3450400665430943309818061)
            ·
              refine ⟨1293900249536603741181773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3450400665430943309818061 1293900249536603741181773)
              ·
                refine ⟨485212593576226402943165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1293900249536603741181773 485212593576226402943165)
                ·
                  refine ⟨181954722591084901103687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485212593576226402943165 181954722591084901103687)
                  ·
                    rfl

theorem cell20_398650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_398650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398650 prefixEnd_398650 := by exact prefixLift 398650
  have htrace : WordTrace (prefixWord ++ tailWord_398650) baseStart_398650 baseEnd_398650 := by
    simpa [prefixWord, tailWord_398650, baseEnd_398650] using wordTrace_append hprefix tailTrace_398650
  have hstable : (prefixWord ++ tailWord_398650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398650).length < 2 ^ (prefixWord ++ tailWord_398650).sum := by decide
  have hdescent : baseEnd_398650 < baseStart_398650 := by decide
  rcases family_descends (prefixWord ++ tailWord_398650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398674 : List Nat := [3, 2, 2, 1, 1, 1, 1, 7, 2]
def baseStart_398674 : Nat := 118140960795 + 398674 * 2 ^ 59
def prefixEnd_398674 : Nat := 4983230072969 + 3 ^ 40 * 398674 * 2
def baseEnd_398674 : Nat := 181965676845047484303589

theorem tailTrace_398674 : CollatzResearch.WordTrace tailWord_398674 prefixEnd_398674 181965676845047484303589 := by
  unfold tailWord_398674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3635208839419915235884769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9693890238453107295692717 3635208839419915235884769)
  ·
    refine ⟨2726406629564936426913577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3635208839419915235884769 2726406629564936426913577)
    ·
      refine ⟨2044804972173702320185183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2726406629564936426913577 2044804972173702320185183)
      ·
        refine ⟨3067207458260553480277775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2044804972173702320185183 3067207458260553480277775)
        ·
          refine ⟨4600811187390830220416663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3067207458260553480277775 4600811187390830220416663)
          ·
            refine ⟨6901216781086245330624995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600811187390830220416663 6901216781086245330624995)
            ·
              refine ⟨10351825171629367995937493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6901216781086245330624995 10351825171629367995937493)
              ·
                refine ⟨242620902460063312404785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10351825171629367995937493 242620902460063312404785)
                ·
                  refine ⟨181965676845047484303589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242620902460063312404785 181965676845047484303589)
                  ·
                    rfl

theorem cell20_398674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_398674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398674 prefixEnd_398674 := by exact prefixLift 398674
  have htrace : WordTrace (prefixWord ++ tailWord_398674) baseStart_398674 baseEnd_398674 := by
    simpa [prefixWord, tailWord_398674, baseEnd_398674] using wordTrace_append hprefix tailTrace_398674
  have hstable : (prefixWord ++ tailWord_398674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398674).length < 2 ^ (prefixWord ++ tailWord_398674).sum := by decide
  have hdescent : baseEnd_398674 < baseStart_398674 := by decide
  rcases family_descends (prefixWord ++ tailWord_398674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398688 : List Nat := [2, 1, 1, 3, 4, 1, 1, 4, 3]
def baseStart_398688 : Nat := 118140960795 + 398688 * 2 ^ 59
def prefixEnd_398688 : Nat := 4983230072969 + 3 ^ 40 * 398688 * 2
def baseEnd_398688 : Nat := 181972066826525657836865

theorem tailTrace_398688 : CollatzResearch.WordTrace tailWord_398688 prefixEnd_398688 181972066826525657836865 := by
  unfold tailWord_398688
  simp only [CollatzResearch.WordTrace]
  refine ⟨7270672989814470667274359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9694230653085960889699145 7270672989814470667274359)
  ·
    refine ⟨10906009484721706000911539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7270672989814470667274359 10906009484721706000911539)
    ·
      refine ⟨16359014227082559001367309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10906009484721706000911539 16359014227082559001367309)
      ·
        refine ⟨6134630335155959625512741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16359014227082559001367309 6134630335155959625512741)
        ·
          refine ⟨1150243187841742429783639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6134630335155959625512741 1150243187841742429783639)
          ·
            refine ⟨1725364781762613644675459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150243187841742429783639 1725364781762613644675459)
            ·
              refine ⟨2588047172643920467013189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725364781762613644675459 2588047172643920467013189)
              ·
                refine ⟨485258844870735087564973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2588047172643920467013189 485258844870735087564973)
                ·
                  refine ⟨181972066826525657836865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485258844870735087564973 181972066826525657836865)
                  ·
                    rfl

theorem cell20_398688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_398688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398688 prefixEnd_398688 := by exact prefixLift 398688
  have htrace : WordTrace (prefixWord ++ tailWord_398688) baseStart_398688 baseEnd_398688 := by
    simpa [prefixWord, tailWord_398688, baseEnd_398688] using wordTrace_append hprefix tailTrace_398688
  have hstable : (prefixWord ++ tailWord_398688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398688).length < 2 ^ (prefixWord ++ tailWord_398688).sum := by decide
  have hdescent : baseEnd_398688 < baseStart_398688 := by decide
  rcases family_descends (prefixWord ++ tailWord_398688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398691 : List Nat := [1, 1, 1, 5, 2, 2, 4, 2, 2]
def baseStart_398691 : Nat := 118140960795 + 398691 * 2 ^ 59
def prefixEnd_398691 : Nat := 4983230072969 + 3 ^ 40 * 398691 * 2
def baseEnd_398691 : Nat := 181973436108270980736853

theorem tailTrace_398691 : CollatzResearch.WordTrace tailWord_398691 prefixEnd_398691 181973436108270980736853 := by
  unfold tailWord_398691
  simp only [CollatzResearch.WordTrace]
  refine ⟨14541455398618072846907927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9694303599078715231271951 14541455398618072846907927)
  ·
    refine ⟨21812183097927109270361891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14541455398618072846907927 21812183097927109270361891)
    ·
      refine ⟨32718274646890663905542837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21812183097927109270361891 32718274646890663905542837)
      ·
        refine ⟨3067338248145999741144641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32718274646890663905542837 3067338248145999741144641)
        ·
          refine ⟨2300503686109499805858481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3067338248145999741144641 2300503686109499805858481)
          ·
            refine ⟨1725377764582124854393861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2300503686109499805858481 1725377764582124854393861)
            ·
              refine ⟨323508330859148410198849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1725377764582124854393861 323508330859148410198849)
              ·
                refine ⟨242631248144361307649137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323508330859148410198849 242631248144361307649137)
                ·
                  refine ⟨181973436108270980736853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242631248144361307649137 181973436108270980736853)
                  ·
                    rfl

theorem cell20_398691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 2].length) (baseStart_398691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398691 prefixEnd_398691 := by exact prefixLift 398691
  have htrace : WordTrace (prefixWord ++ tailWord_398691) baseStart_398691 baseEnd_398691 := by
    simpa [prefixWord, tailWord_398691, baseEnd_398691] using wordTrace_append hprefix tailTrace_398691
  have hstable : (prefixWord ++ tailWord_398691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398691).length < 2 ^ (prefixWord ++ tailWord_398691).sum := by decide
  have hdescent : baseEnd_398691 < baseStart_398691 := by decide
  rcases family_descends (prefixWord ++ tailWord_398691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398698 : List Nat := [3, 1, 3, 3, 2, 2, 1, 5]
def baseStart_398698 : Nat := 118140960795 + 398698 * 2 ^ 59
def prefixEnd_398698 : Nat := 4983230072969 + 3 ^ 40 * 398698 * 2
def baseEnd_398698 : Nat := 60658877033003355834497

theorem tailTrace_398698 : CollatzResearch.WordTrace tailWord_398698 prefixEnd_398698 60658877033003355834497 := by
  unfold tailWord_398698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3635427677398178260603187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9694473806395142028275165 3635427677398178260603187)
  ·
    refine ⟨5453141516097267390904781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3635427677398178260603187 5453141516097267390904781)
    ·
      refine ⟨2044928068536475271589293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5453141516097267390904781 2044928068536475271589293)
      ·
        refine ⟨766848025701178226845985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2044928068536475271589293 766848025701178226845985)
        ·
          refine ⟨575136019275883670134489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 766848025701178226845985 575136019275883670134489)
          ·
            refine ⟨431352014456912752600867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575136019275883670134489 431352014456912752600867)
            ·
              refine ⟨647028021685369128901301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431352014456912752600867 647028021685369128901301)
              ·
                refine ⟨60658877033003355834497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 647028021685369128901301 60658877033003355834497)
                ·
                  rfl

theorem cell20_398698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_398698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398698 prefixEnd_398698 := by exact prefixLift 398698
  have htrace : WordTrace (prefixWord ++ tailWord_398698) baseStart_398698 baseEnd_398698 := by
    simpa [prefixWord, tailWord_398698, baseEnd_398698] using wordTrace_append hprefix tailTrace_398698
  have hstable : (prefixWord ++ tailWord_398698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398698).length < 2 ^ (prefixWord ++ tailWord_398698).sum := by decide
  have hdescent : baseEnd_398698 < baseStart_398698 := by decide
  rcases family_descends (prefixWord ++ tailWord_398698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398729 : List Nat := [1, 2, 1, 1, 7, 1, 2, 3, 2]
def baseStart_398729 : Nat := 118140960795 + 398729 * 2 ^ 59
def prefixEnd_398729 : Nat := 4983230072969 + 3 ^ 40 * 398729 * 2
def baseEnd_398729 : Nat := 181990780343711737470031

theorem tailTrace_398729 : CollatzResearch.WordTrace tailWord_398729 prefixEnd_398729 181990780343711737470031 := by
  unfold tailWord_398729
  simp only [CollatzResearch.WordTrace]
  refine ⟨14542841372480405336791241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9695227581653603557860827 14542841372480405336791241)
  ·
    refine ⟨10907131029360304002593431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14542841372480405336791241 10907131029360304002593431)
    ·
      refine ⟨16360696544040456003890147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10907131029360304002593431 16360696544040456003890147)
      ·
        refine ⟨24541044816060684005835221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16360696544040456003890147 24541044816060684005835221)
        ·
          refine ⟨575180737876422281386763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 24541044816060684005835221 575180737876422281386763)
          ·
            refine ⟨862771106814633422080145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575180737876422281386763 862771106814633422080145)
            ·
              refine ⟨647078330110975066560109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 862771106814633422080145 647078330110975066560109)
              ·
                refine ⟨242654373791615649960041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 647078330110975066560109 242654373791615649960041)
                ·
                  refine ⟨181990780343711737470031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242654373791615649960041 181990780343711737470031)
                  ·
                    rfl

theorem cell20_398729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 2].length) (baseStart_398729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398729 prefixEnd_398729 := by exact prefixLift 398729
  have htrace : WordTrace (prefixWord ++ tailWord_398729) baseStart_398729 baseEnd_398729 := by
    simpa [prefixWord, tailWord_398729, baseEnd_398729] using wordTrace_append hprefix tailTrace_398729
  have hstable : (prefixWord ++ tailWord_398729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398729).length < 2 ^ (prefixWord ++ tailWord_398729).sum := by decide
  have hdescent : baseEnd_398729 < baseStart_398729 := by decide
  rcases family_descends (prefixWord ++ tailWord_398729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398799 : List Nat := [1, 1, 2, 1, 1, 4, 10]
def baseStart_398799 : Nat := 118140960795 + 398799 * 2 ^ 59
def prefixEnd_398799 : Nat := 4983230072969 + 3 ^ 40 * 398799 * 2
def baseEnd_398799 : Nat := 20224747805678067237379

theorem tailTrace_398799 : CollatzResearch.WordTrace tailWord_398799 prefixEnd_398799 20224747805678067237379 := by
  unfold tailWord_398799
  simp only [CollatzResearch.WordTrace]
  refine ⟨14545394482226807291839451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9696929654817871527892967 14545394482226807291839451)
  ·
    refine ⟨21818091723340210937759177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14545394482226807291839451 21818091723340210937759177)
    ·
      refine ⟨16363568792505158203319383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21818091723340210937759177 16363568792505158203319383)
      ·
        refine ⟨24545353188757737304979075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16363568792505158203319383 24545353188757737304979075)
        ·
          refine ⟨36818029783136605957468613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24545353188757737304979075 36818029783136605957468613)
          ·
            refine ⟨6903380584338113617025365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36818029783136605957468613 6903380584338113617025365)
            ·
              refine ⟨20224747805678067237379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6903380584338113617025365 20224747805678067237379)
              ·
                rfl

theorem cell20_398799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 10].length) (baseStart_398799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398799 prefixEnd_398799 := by exact prefixLift 398799
  have htrace : WordTrace (prefixWord ++ tailWord_398799) baseStart_398799 baseEnd_398799 := by
    simpa [prefixWord, tailWord_398799, baseEnd_398799] using wordTrace_append hprefix tailTrace_398799
  have hstable : (prefixWord ++ tailWord_398799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398799).length < 2 ^ (prefixWord ++ tailWord_398799).sum := by decide
  have hdescent : baseEnd_398799 < baseStart_398799 := by decide
  rcases family_descends (prefixWord ++ tailWord_398799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398805 : List Nat := [1, 3, 2, 3, 1, 1, 5, 2, 2]
def baseStart_398805 : Nat := 118140960795 + 398805 * 2 ^ 59
def prefixEnd_398805 : Nat := 4983230072969 + 3 ^ 40 * 398805 * 2
def baseEnd_398805 : Nat := 182025468814593250936387

theorem tailTrace_398805 : CollatzResearch.WordTrace tailWord_398805 prefixEnd_398805 182025468814593250936387 := by
  unfold tailWord_398805
  simp only [CollatzResearch.WordTrace]
  refine ⟨14545613320205070316557869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9697075546803380211038579 14545613320205070316557869)
  ·
    refine ⟨5454604995076901368709201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14545613320205070316557869 5454604995076901368709201)
    ·
      refine ⟨4090953746307676026531901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5454604995076901368709201 4090953746307676026531901)
      ·
        refine ⟨1534107654865378509949463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4090953746307676026531901 1534107654865378509949463)
        ·
          refine ⟨2301161482298067764924195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534107654865378509949463 2301161482298067764924195)
          ·
            refine ⟨3451742223447101647386293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301161482298067764924195 3451742223447101647386293)
            ·
              refine ⟨323600833448165779442465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3451742223447101647386293 323600833448165779442465)
              ·
                refine ⟨242700625086124334581849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323600833448165779442465 242700625086124334581849)
                ·
                  refine ⟨182025468814593250936387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242700625086124334581849 182025468814593250936387)
                  ·
                    rfl

theorem cell20_398805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_398805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398805 prefixEnd_398805 := by exact prefixLift 398805
  have htrace : WordTrace (prefixWord ++ tailWord_398805) baseStart_398805 baseEnd_398805 := by
    simpa [prefixWord, tailWord_398805, baseEnd_398805] using wordTrace_append hprefix tailTrace_398805
  have hstable : (prefixWord ++ tailWord_398805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398805).length < 2 ^ (prefixWord ++ tailWord_398805).sum := by decide
  have hdescent : baseEnd_398805 < baseStart_398805 := by decide
  rcases family_descends (prefixWord ++ tailWord_398805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398809 : List Nat := [1, 2, 1, 2, 4, 2, 3, 1, 4]
def baseStart_398809 : Nat := 118140960795 + 398809 * 2 ^ 59
def prefixEnd_398809 : Nat := 4983230072969 + 3 ^ 40 * 398809 * 2
def baseEnd_398809 : Nat := 182027294523587014803037

theorem tailTrace_398809 : CollatzResearch.WordTrace tailWord_398809 prefixEnd_398809 182027294523587014803037 := by
  unfold tailWord_398809
  simp only [CollatzResearch.WordTrace]
  refine ⟨14545759212190578999703481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9697172808127052666468987 14545759212190578999703481)
  ·
    refine ⟨10909319409142934249777611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14545759212190578999703481 10909319409142934249777611)
    ·
      refine ⟨16363979113714401374666417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10909319409142934249777611 16363979113714401374666417)
      ·
        refine ⟨12272984335285801030999813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16363979113714401374666417 12272984335285801030999813)
        ·
          refine ⟨2301184562866087693312465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12272984335285801030999813 2301184562866087693312465)
          ·
            refine ⟨1725888422149565769984349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2301184562866087693312465 1725888422149565769984349)
            ·
              refine ⟨647208158306087163744131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1725888422149565769984349 647208158306087163744131)
              ·
                refine ⟨970812237459130745616197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647208158306087163744131 970812237459130745616197)
                ·
                  refine ⟨182027294523587014803037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 970812237459130745616197 182027294523587014803037)
                  ·
                    rfl

theorem cell20_398809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_398809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398809 prefixEnd_398809 := by exact prefixLift 398809
  have htrace : WordTrace (prefixWord ++ tailWord_398809) baseStart_398809 baseEnd_398809 := by
    simpa [prefixWord, tailWord_398809, baseEnd_398809] using wordTrace_append hprefix tailTrace_398809
  have hstable : (prefixWord ++ tailWord_398809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398809).length < 2 ^ (prefixWord ++ tailWord_398809).sum := by decide
  have hdescent : baseEnd_398809 < baseStart_398809 := by decide
  rcases family_descends (prefixWord ++ tailWord_398809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398819 : List Nat := [1, 1, 1, 6, 2, 1, 4, 1, 3]
def baseStart_398819 : Nat := 118140960795 + 398819 * 2 ^ 59
def prefixEnd_398819 : Nat := 4983230072969 + 3 ^ 40 * 398819 * 2
def baseEnd_398819 : Nat := 182031858796071424469663

theorem tailTrace_398819 : CollatzResearch.WordTrace tailWord_398819 prefixEnd_398819 182031858796071424469663 := by
  unfold tailWord_398819
  simp only [CollatzResearch.WordTrace]
  refine ⟨14546123942154350707567511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9697415961436233805045007 14546123942154350707567511)
  ·
    refine ⟨21819185913231526061351267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14546123942154350707567511 21819185913231526061351267)
    ·
      refine ⟨32728778869847289092026901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21819185913231526061351267 32728778869847289092026901)
      ·
        refine ⟨1534161509524091676188761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32728778869847289092026901 1534161509524091676188761)
        ·
          refine ⟨1150621132143068757141571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1534161509524091676188761 1150621132143068757141571)
          ·
            refine ⟨1725931698214603135712357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150621132143068757141571 1725931698214603135712357)
            ·
              refine ⟨323612193415238087946067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1725931698214603135712357 323612193415238087946067)
              ·
                refine ⟨485418290122857131919101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323612193415238087946067 485418290122857131919101)
                ·
                  refine ⟨182031858796071424469663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485418290122857131919101 182031858796071424469663)
                  ·
                    rfl

theorem cell20_398819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 3].length) (baseStart_398819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398819 prefixEnd_398819 := by exact prefixLift 398819
  have htrace : WordTrace (prefixWord ++ tailWord_398819) baseStart_398819 baseEnd_398819 := by
    simpa [prefixWord, tailWord_398819, baseEnd_398819] using wordTrace_append hprefix tailTrace_398819
  have hstable : (prefixWord ++ tailWord_398819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398819).length < 2 ^ (prefixWord ++ tailWord_398819).sum := by decide
  have hdescent : baseEnd_398819 < baseStart_398819 := by decide
  rcases family_descends (prefixWord ++ tailWord_398819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398860 : List Nat := [2, 2, 1, 2, 5, 2, 2, 2, 2]
def baseStart_398860 : Nat := 118140960795 + 398860 * 2 ^ 59
def prefixEnd_398860 : Nat := 4983230072969 + 3 ^ 40 * 398860 * 2
def baseEnd_398860 : Nat := 182050572313257504102829

theorem tailTrace_398860 : CollatzResearch.WordTrace tailWord_398860 prefixEnd_398860 182050572313257504102829 := by
  unfold tailWord_398860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7273809667502907354905017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9698412890003876473206689 7273809667502907354905017)
  ·
    refine ⟨5455357250627180516178763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7273809667502907354905017 5455357250627180516178763)
    ·
      refine ⟨8183035875940770774268145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5455357250627180516178763 8183035875940770774268145)
      ·
        refine ⟨6137276906955578080701109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8183035875940770774268145 6137276906955578080701109)
        ·
          refine ⟨575369710027085445065729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6137276906955578080701109 575369710027085445065729)
          ·
            refine ⟨431527282520314083799297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575369710027085445065729 431527282520314083799297)
            ·
              refine ⟨323645461890235562849473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431527282520314083799297 323645461890235562849473)
              ·
                refine ⟨242734096417676672137105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323645461890235562849473 242734096417676672137105)
                ·
                  refine ⟨182050572313257504102829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242734096417676672137105 182050572313257504102829)
                  ·
                    rfl

theorem cell20_398860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_398860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398860 prefixEnd_398860 := by exact prefixLift 398860
  have htrace : WordTrace (prefixWord ++ tailWord_398860) baseStart_398860 baseEnd_398860 := by
    simpa [prefixWord, tailWord_398860, baseEnd_398860] using wordTrace_append hprefix tailTrace_398860
  have hstable : (prefixWord ++ tailWord_398860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398860).length < 2 ^ (prefixWord ++ tailWord_398860).sum := by decide
  have hdescent : baseEnd_398860 < baseStart_398860 := by decide
  rcases family_descends (prefixWord ++ tailWord_398860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398888 : List Nat := [2, 1, 5, 2, 2, 1, 3, 4]
def baseStart_398888 : Nat := 118140960795 + 398888 * 2 ^ 59
def prefixEnd_398888 : Nat := 4983230072969 + 3 ^ 40 * 398888 * 2
def baseEnd_398888 : Nat := 60687784092071283723127

theorem tailTrace_398888 : CollatzResearch.WordTrace tailWord_398888 prefixEnd_398888 60687784092071283723127 := by
  unfold tailWord_398888
  simp only [CollatzResearch.WordTrace]
  refine ⟨7274320289452187745914659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9699093719269583661219545 7274320289452187745914659)
  ·
    refine ⟨10911480434178281618871989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7274320289452187745914659 10911480434178281618871989)
    ·
      refine ⟨1022951290704213901769249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10911480434178281618871989 1022951290704213901769249)
      ·
        refine ⟨767213468028160426326937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1022951290704213901769249 767213468028160426326937)
        ·
          refine ⟨575410101021120319745203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767213468028160426326937 575410101021120319745203)
          ·
            refine ⟨863115151531680479617805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575410101021120319745203 863115151531680479617805)
            ·
              refine ⟨323668181824380179856677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 863115151531680479617805 323668181824380179856677)
              ·
                refine ⟨60687784092071283723127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323668181824380179856677 60687784092071283723127)
                ·
                  rfl

theorem cell20_398888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_398888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398888 prefixEnd_398888 := by exact prefixLift 398888
  have htrace : WordTrace (prefixWord ++ tailWord_398888) baseStart_398888 baseEnd_398888 := by
    simpa [prefixWord, tailWord_398888, baseEnd_398888] using wordTrace_append hprefix tailTrace_398888
  have hstable : (prefixWord ++ tailWord_398888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398888).length < 2 ^ (prefixWord ++ tailWord_398888).sum := by decide
  have hdescent : baseEnd_398888 < baseStart_398888 := by decide
  rcases family_descends (prefixWord ++ tailWord_398888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398906 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_398906 : Nat := 118140960795 + 398906 * 2 ^ 59
def prefixEnd_398906 : Nat := 4983230072969 + 3 ^ 40 * 398906 * 2
def baseEnd_398906 : Nat := 182071567966685788569307

theorem tailTrace_398906 : CollatzResearch.WordTrace tailWord_398906 prefixEnd_398906 182071567966685788569307 := by
  unfold tailWord_398906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3637324273209791141496143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9699531395226109710656381 3637324273209791141496143)
  ·
    refine ⟨5455986409814686712244215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3637324273209791141496143 5455986409814686712244215)
    ·
      refine ⟨8183979614722030068366323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5455986409814686712244215 8183979614722030068366323)
      ·
        refine ⟨12275969422083045102549485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8183979614722030068366323 12275969422083045102549485)
        ·
          refine ⟨4603488533281141913456057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12275969422083045102549485 4603488533281141913456057)
          ·
            refine ⟨3452616399960856435092043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4603488533281141913456057 3452616399960856435092043)
            ·
              refine ⟨5178924599941284652638065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3452616399960856435092043 5178924599941284652638065)
              ·
                refine ⟨3884193449955963489478549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5178924599941284652638065 3884193449955963489478549)
                ·
                  refine ⟨182071567966685788569307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3884193449955963489478549 182071567966685788569307)
                  ·
                    rfl

theorem cell20_398906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_398906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398906 prefixEnd_398906 := by exact prefixLift 398906
  have htrace : WordTrace (prefixWord ++ tailWord_398906) baseStart_398906 baseEnd_398906 := by
    simpa [prefixWord, tailWord_398906, baseEnd_398906] using wordTrace_append hprefix tailTrace_398906
  have hstable : (prefixWord ++ tailWord_398906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398906).length < 2 ^ (prefixWord ++ tailWord_398906).sum := by decide
  have hdescent : baseEnd_398906 < baseStart_398906 := by decide
  rcases family_descends (prefixWord ++ tailWord_398906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398937 : List Nat := [1, 2, 1, 2, 2, 1, 1, 7, 3]
def baseStart_398937 : Nat := 118140960795 + 398937 * 2 ^ 59
def prefixEnd_398937 : Nat := 4983230072969 + 3 ^ 40 * 398937 * 2
def baseEnd_398937 : Nat := 182085717211387458535847

theorem tailTrace_398937 : CollatzResearch.WordTrace tailWord_398937 prefixEnd_398937 182085717211387458535847 := by
  unfold tailWord_398937
  simp only [CollatzResearch.WordTrace]
  refine ⟨14550427755726856860363065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9700285170484571240242043 14550427755726856860363065)
  ·
    refine ⟨10912820816795142645272299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14550427755726856860363065 10912820816795142645272299)
    ·
      refine ⟨16369231225192713967908449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10912820816795142645272299 16369231225192713967908449)
      ·
        refine ⟨12276923418894535475931337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16369231225192713967908449 12276923418894535475931337)
        ·
          refine ⟨9207692564170901606948503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12276923418894535475931337 9207692564170901606948503)
          ·
            refine ⟨13811538846256352410422755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9207692564170901606948503 13811538846256352410422755)
            ·
              refine ⟨20717308269384528615634133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13811538846256352410422755 20717308269384528615634133)
              ·
                refine ⟨485561912563699889428925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20717308269384528615634133 485561912563699889428925)
                ·
                  refine ⟨182085717211387458535847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485561912563699889428925 182085717211387458535847)
                  ·
                    rfl

theorem cell20_398937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_398937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398937 prefixEnd_398937 := by exact prefixLift 398937
  have htrace : WordTrace (prefixWord ++ tailWord_398937) baseStart_398937 baseEnd_398937 := by
    simpa [prefixWord, tailWord_398937, baseEnd_398937] using wordTrace_append hprefix tailTrace_398937
  have hstable : (prefixWord ++ tailWord_398937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398937).length < 2 ^ (prefixWord ++ tailWord_398937).sum := by decide
  have hdescent : baseEnd_398937 < baseStart_398937 := by decide
  rcases family_descends (prefixWord ++ tailWord_398937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398947 : List Nat := [1, 1, 1, 5, 1, 5, 2, 4]
def baseStart_398947 : Nat := 118140960795 + 398947 * 2 ^ 59
def prefixEnd_398947 : Nat := 4983230072969 + 3 ^ 40 * 398947 * 2
def baseEnd_398947 : Nat := 60696760494623956067491

theorem tailTrace_398947 : CollatzResearch.WordTrace tailWord_398947 prefixEnd_398947 60696760494623956067491 := by
  unfold tailWord_398947
  simp only [CollatzResearch.WordTrace]
  refine ⟨14550792485690628568227095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9700528323793752378818063 14550792485690628568227095)
  ·
    refine ⟨21826188728535942852340643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14550792485690628568227095 21826188728535942852340643)
    ·
      refine ⟨32739283092803914278510965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21826188728535942852340643 32739283092803914278510965)
      ·
        refine ⟨3069307789950366963610403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32739283092803914278510965 3069307789950366963610403)
        ·
          refine ⟨4603961684925550445415605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3069307789950366963610403 4603961684925550445415605)
          ·
            refine ⟨431621407961770354257713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4603961684925550445415605 431621407961770354257713)
            ·
              refine ⟨323716055971327765693285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431621407961770354257713 323716055971327765693285)
              ·
                refine ⟨60696760494623956067491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323716055971327765693285 60696760494623956067491)
                ·
                  rfl

theorem cell20_398947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 4].length) (baseStart_398947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_398947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_398947 prefixEnd_398947 := by exact prefixLift 398947
  have htrace : WordTrace (prefixWord ++ tailWord_398947) baseStart_398947 baseEnd_398947 := by
    simpa [prefixWord, tailWord_398947, baseEnd_398947] using wordTrace_append hprefix tailTrace_398947
  have hstable : (prefixWord ++ tailWord_398947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398947).length < 2 ^ (prefixWord ++ tailWord_398947).sum := by decide
  have hdescent : baseEnd_398947 < baseStart_398947 := by decide
  rcases family_descends (prefixWord ++ tailWord_398947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399029 : List Nat := [1, 3, 3, 3, 3, 1, 2, 2, 2]
def baseStart_399029 : Nat := 118140960795 + 399029 * 2 ^ 59
def prefixEnd_399029 : Nat := 4983230072969 + 3 ^ 40 * 399029 * 2
def baseEnd_399029 : Nat := 182127708518244027468805

theorem tailTrace_399029 : CollatzResearch.WordTrace tailWord_399029 prefixEnd_399029 182127708518244027468805 := by
  unfold tailWord_399029
  simp only [CollatzResearch.WordTrace]
  refine ⟨14553783271393556572712141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9702522180929037715141427 14553783271393556572712141)
  ·
    refine ⟨5457668726772583714767053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14553783271393556572712141 5457668726772583714767053)
    ·
      refine ⟨2046625772539718893037645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5457668726772583714767053 2046625772539718893037645)
      ·
        refine ⟨767484664702394584889117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2046625772539718893037645 767484664702394584889117)
        ·
          refine ⟨287806749263397969333419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 767484664702394584889117 287806749263397969333419)
          ·
            refine ⟨431710123895096954000129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287806749263397969333419 431710123895096954000129)
            ·
              refine ⟨323782592921322715500097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431710123895096954000129 323782592921322715500097)
              ·
                refine ⟨242836944690992036625073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323782592921322715500097 242836944690992036625073)
                ·
                  refine ⟨182127708518244027468805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242836944690992036625073 182127708518244027468805)
                  ·
                    rfl

theorem cell20_399029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_399029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399029 prefixEnd_399029 := by exact prefixLift 399029
  have htrace : WordTrace (prefixWord ++ tailWord_399029) baseStart_399029 baseEnd_399029 := by
    simpa [prefixWord, tailWord_399029, baseEnd_399029] using wordTrace_append hprefix tailTrace_399029
  have hstable : (prefixWord ++ tailWord_399029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399029).length < 2 ^ (prefixWord ++ tailWord_399029).sum := by decide
  have hdescent : baseEnd_399029 < baseStart_399029 := by decide
  rcases family_descends (prefixWord ++ tailWord_399029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399085 : List Nat := [1, 5, 1, 2, 1, 4, 1, 2, 3]
def baseStart_399085 : Nat := 118140960795 + 399085 * 2 ^ 59
def prefixEnd_399085 : Nat := 4983230072969 + 3 ^ 40 * 399085 * 2
def baseEnd_399085 : Nat := 182153268444156721601909

theorem tailTrace_399085 : CollatzResearch.WordTrace tailWord_399085 prefixEnd_399085 182153268444156721601909 := by
  unfold tailWord_399085
  simp only [CollatzResearch.WordTrace]
  refine ⟨14555825759190678136750709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9703883839460452091167139 14555825759190678136750709)
  ·
    refine ⟨1364608664924126075320379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14555825759190678136750709 1364608664924126075320379)
    ·
      refine ⟨2046912997386189112980569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1364608664924126075320379 2046912997386189112980569)
      ·
        refine ⟨1535184748039641834735427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2046912997386189112980569 1535184748039641834735427)
        ·
          refine ⟨2302777122059462752103141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1535184748039641834735427 2302777122059462752103141)
          ·
            refine ⟨431770710386149266019339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2302777122059462752103141 431770710386149266019339)
            ·
              refine ⟨647656065579223899029009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431770710386149266019339 647656065579223899029009)
              ·
                refine ⟨485742049184417924271757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 647656065579223899029009 485742049184417924271757)
                ·
                  refine ⟨182153268444156721601909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485742049184417924271757 182153268444156721601909)
                  ·
                    rfl

theorem cell20_399085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_399085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399085 prefixEnd_399085 := by exact prefixLift 399085
  have htrace : WordTrace (prefixWord ++ tailWord_399085) baseStart_399085 baseEnd_399085 := by
    simpa [prefixWord, tailWord_399085, baseEnd_399085] using wordTrace_append hprefix tailTrace_399085
  have hstable : (prefixWord ++ tailWord_399085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399085).length < 2 ^ (prefixWord ++ tailWord_399085).sum := by decide
  have hdescent : baseEnd_399085 < baseStart_399085 := by decide
  rcases family_descends (prefixWord ++ tailWord_399085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399089 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 5]
def baseStart_399089 : Nat := 118140960795 + 399089 * 2 ^ 59
def prefixEnd_399089 : Nat := 4983230072969 + 3 ^ 40 * 399089 * 2
def baseEnd_399089 : Nat := 182155094153150485468559

theorem tailTrace_399089 : CollatzResearch.WordTrace tailWord_399089 prefixEnd_399089 182155094153150485468559 := by
  unfold tailWord_399089
  simp only [CollatzResearch.WordTrace]
  refine ⟨14555971651176186819896321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9703981100784124546597547 14555971651176186819896321)
  ·
    refine ⟨10916978738382140114922241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14555971651176186819896321 10916978738382140114922241)
    ·
      refine ⟨8187734053786605086191681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10916978738382140114922241 8187734053786605086191681)
      ·
        refine ⟨6140800540339953814643761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8187734053786605086191681 6140800540339953814643761)
        ·
          refine ⟨4605600405254965360982821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6140800540339953814643761 4605600405254965360982821)
          ·
            refine ⟨863550075985306005184279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4605600405254965360982821 863550075985306005184279)
            ·
              refine ⟨1295325113977959007776419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863550075985306005184279 1295325113977959007776419)
              ·
                refine ⟨1942987670966938511664629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295325113977959007776419 1942987670966938511664629)
                ·
                  refine ⟨182155094153150485468559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1942987670966938511664629 182155094153150485468559)
                  ·
                    rfl

theorem cell20_399089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_399089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399089 prefixEnd_399089 := by exact prefixLift 399089
  have htrace : WordTrace (prefixWord ++ tailWord_399089) baseStart_399089 baseEnd_399089 := by
    simpa [prefixWord, tailWord_399089, baseEnd_399089] using wordTrace_append hprefix tailTrace_399089
  have hstable : (prefixWord ++ tailWord_399089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399089).length < 2 ^ (prefixWord ++ tailWord_399089).sum := by decide
  have hdescent : baseEnd_399089 < baseStart_399089 := by decide
  rcases family_descends (prefixWord ++ tailWord_399089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399102 : List Nat := [4, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_399102 : Nat := 118140960795 + 399102 * 2 ^ 59
def prefixEnd_399102 : Nat := 4983230072969 + 3 ^ 40 * 399102 * 2
def baseEnd_399102 : Nat := 182161027707380218035173

theorem tailTrace_399102 : CollatzResearch.WordTrace tailWord_399102 prefixEnd_399102 182161027707380218035173 := by
  unfold tailWord_399102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1819555725016136255014945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9704297200086060026746373 1819555725016136255014945)
  ·
    refine ⟨1364666793762102191261209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1819555725016136255014945 1364666793762102191261209)
    ·
      refine ⟨1023500095321576643445907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1364666793762102191261209 1023500095321576643445907)
      ·
        refine ⟨1535250142982364965168861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1023500095321576643445907 1535250142982364965168861)
        ·
          refine ⟨575718803618386861938323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1535250142982364965168861 575718803618386861938323)
          ·
            refine ⟨863578205427580292907485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575718803618386861938323 863578205427580292907485)
            ·
              refine ⟨323841827035342609840307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 863578205427580292907485 323841827035342609840307)
              ·
                refine ⟨485762740553013914760461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323841827035342609840307 485762740553013914760461)
                ·
                  refine ⟨182161027707380218035173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485762740553013914760461 182161027707380218035173)
                  ·
                    rfl

theorem cell20_399102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_399102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399102 prefixEnd_399102 := by exact prefixLift 399102
  have htrace : WordTrace (prefixWord ++ tailWord_399102) baseStart_399102 baseEnd_399102 := by
    simpa [prefixWord, tailWord_399102, baseEnd_399102] using wordTrace_append hprefix tailTrace_399102
  have hstable : (prefixWord ++ tailWord_399102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399102).length < 2 ^ (prefixWord ++ tailWord_399102).sum := by decide
  have hdescent : baseEnd_399102 < baseStart_399102 := by decide
  rcases family_descends (prefixWord ++ tailWord_399102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399127 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 5]
def baseStart_399127 : Nat := 118140960795 + 399127 * 2 ^ 59
def prefixEnd_399127 : Nat := 4983230072969 + 3 ^ 40 * 399127 * 2
def baseEnd_399127 : Nat := 182172438388591242201737

theorem tailTrace_399127 : CollatzResearch.WordTrace tailWord_399127 prefixEnd_399127 182172438388591242201737 := by
  unfold tailWord_399127
  simp only [CollatzResearch.WordTrace]
  refine ⟨14557357625038519309779635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9704905083359012873186423 14557357625038519309779635)
  ·
    refine ⟨21836036437557778964669453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14557357625038519309779635 21836036437557778964669453)
    ·
      refine ⟨8188513664084167111751045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21836036437557778964669453 8188513664084167111751045)
      ·
        refine ⟨1535346312015781333453321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8188513664084167111751045 1535346312015781333453321)
        ·
          refine ⟨1151509734011836000089991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1535346312015781333453321 1151509734011836000089991)
          ·
            refine ⟨1727264601017754000134987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151509734011836000089991 1727264601017754000134987)
            ·
              refine ⟨2590896901526631000202481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1727264601017754000134987 2590896901526631000202481)
              ·
                refine ⟨1943172676144973250151861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2590896901526631000202481 1943172676144973250151861)
                ·
                  refine ⟨182172438388591242201737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1943172676144973250151861 182172438388591242201737)
                  ·
                    rfl

theorem cell20_399127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_399127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399127 prefixEnd_399127 := by exact prefixLift 399127
  have htrace : WordTrace (prefixWord ++ tailWord_399127) baseStart_399127 baseEnd_399127 := by
    simpa [prefixWord, tailWord_399127, baseEnd_399127] using wordTrace_append hprefix tailTrace_399127
  have hstable : (prefixWord ++ tailWord_399127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399127).length < 2 ^ (prefixWord ++ tailWord_399127).sum := by decide
  have hdescent : baseEnd_399127 < baseStart_399127 := by decide
  rcases family_descends (prefixWord ++ tailWord_399127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399130 : List Nat := [3, 1, 1, 3, 2, 2, 3, 3, 2]
def baseStart_399130 : Nat := 118140960795 + 399130 * 2 ^ 59
def prefixEnd_399130 : Nat := 4983230072969 + 3 ^ 40 * 399130 * 2
def baseEnd_399130 : Nat := 182173807670336565101725

theorem tailTrace_399130 : CollatzResearch.WordTrace tailWord_399130 prefixEnd_399130 182173807670336565101725 := by
  unfold tailWord_399130
  simp only [CollatzResearch.WordTrace]
  refine ⟨3639366761006912705534711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9704978029351767214759229 3639366761006912705534711)
  ·
    refine ⟨5459050141510369058302067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3639366761006912705534711 5459050141510369058302067)
    ·
      refine ⟨8188575212265553587453101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5459050141510369058302067 8188575212265553587453101)
      ·
        refine ⟨3070715704599582595294913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8188575212265553587453101 3070715704599582595294913)
        ·
          refine ⟨2303036778449686946471185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3070715704599582595294913 2303036778449686946471185)
          ·
            refine ⟨1727277583837265209853389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2303036778449686946471185 1727277583837265209853389)
            ·
              refine ⟨647729093938974453695021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1727277583837265209853389 647729093938974453695021)
              ·
                refine ⟨242898410227115420135633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 647729093938974453695021 242898410227115420135633)
                ·
                  refine ⟨182173807670336565101725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242898410227115420135633 182173807670336565101725)
                  ·
                    rfl

theorem cell20_399130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_399130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399130 prefixEnd_399130 := by exact prefixLift 399130
  have htrace : WordTrace (prefixWord ++ tailWord_399130) baseStart_399130 baseEnd_399130 := by
    simpa [prefixWord, tailWord_399130, baseEnd_399130] using wordTrace_append hprefix tailTrace_399130
  have hstable : (prefixWord ++ tailWord_399130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399130).length < 2 ^ (prefixWord ++ tailWord_399130).sum := by decide
  have hdescent : baseEnd_399130 < baseStart_399130 := by decide
  rcases family_descends (prefixWord ++ tailWord_399130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399141 : List Nat := [1, 3, 1, 2, 3, 2, 8]
def baseStart_399141 : Nat := 118140960795 + 399141 * 2 ^ 59
def prefixEnd_399141 : Nat := 4983230072969 + 3 ^ 40 * 399141 * 2
def baseEnd_399141 : Nat := 20242092041118823970557

theorem tailTrace_399141 : CollatzResearch.WordTrace tailWord_399141 prefixEnd_399141 20242092041118823970557 := by
  unfold tailWord_399141
  simp only [CollatzResearch.WordTrace]
  refine ⟨14557868246987799700789277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9705245497991866467192851 14557868246987799700789277)
  ·
    refine ⟨5459200592620424887795979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14557868246987799700789277 5459200592620424887795979)
    ·
      refine ⟨8188800888930637331693969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5459200592620424887795979 8188800888930637331693969)
      ·
        refine ⟨6141600666697977998770477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8188800888930637331693969 6141600666697977998770477)
        ·
          refine ⟨2303100250011741749538929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6141600666697977998770477 2303100250011741749538929)
          ·
            refine ⟨1727325187508806312154197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2303100250011741749538929 1727325187508806312154197)
            ·
              refine ⟨20242092041118823970557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1727325187508806312154197 20242092041118823970557)
              ·
                rfl

theorem cell20_399141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 8].length) (baseStart_399141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399141 prefixEnd_399141 := by exact prefixLift 399141
  have htrace : WordTrace (prefixWord ++ tailWord_399141) baseStart_399141 baseEnd_399141 := by
    simpa [prefixWord, tailWord_399141, baseEnd_399141] using wordTrace_append hprefix tailTrace_399141
  have hstable : (prefixWord ++ tailWord_399141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399141).length < 2 ^ (prefixWord ++ tailWord_399141).sum := by decide
  have hdescent : baseEnd_399141 < baseStart_399141 := by decide
  rcases family_descends (prefixWord ++ tailWord_399141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399161 : List Nat := [1, 2, 1, 7, 1, 1, 1, 3, 3]
def baseStart_399161 : Nat := 118140960795 + 399161 * 2 ^ 59
def prefixEnd_399161 : Nat := 4983230072969 + 3 ^ 40 * 399161 * 2
def baseEnd_399161 : Nat := 182187956915038235068265

theorem tailTrace_399161 : CollatzResearch.WordTrace tailWord_399161 prefixEnd_399161 182187956915038235068265 := by
  unfold tailWord_399161
  simp only [CollatzResearch.WordTrace]
  refine ⟨14558597706915343116517337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9705731804610228744344891 14558597706915343116517337)
  ·
    refine ⟨10918948280186507337388003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14558597706915343116517337 10918948280186507337388003)
    ·
      refine ⟨16378422420279761006082005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10918948280186507337388003 16378422420279761006082005)
      ·
        refine ⟨383869275475306898580047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 16378422420279761006082005 383869275475306898580047)
        ·
          refine ⟨575803913212960347870071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383869275475306898580047 575803913212960347870071)
          ·
            refine ⟨863705869819440521805107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575803913212960347870071 863705869819440521805107)
            ·
              refine ⟨1295558804729160782707661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863705869819440521805107 1295558804729160782707661)
              ·
                refine ⟨485834551773435293515373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1295558804729160782707661 485834551773435293515373)
                ·
                  refine ⟨182187956915038235068265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485834551773435293515373 182187956915038235068265)
                  ·
                    rfl

theorem cell20_399161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 3].length) (baseStart_399161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399161 prefixEnd_399161 := by exact prefixLift 399161
  have htrace : WordTrace (prefixWord ++ tailWord_399161) baseStart_399161 baseEnd_399161 := by
    simpa [prefixWord, tailWord_399161, baseEnd_399161] using wordTrace_append hprefix tailTrace_399161
  have hstable : (prefixWord ++ tailWord_399161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399161).length < 2 ^ (prefixWord ++ tailWord_399161).sum := by decide
  have hdescent : baseEnd_399161 < baseStart_399161 := by decide
  rcases family_descends (prefixWord ++ tailWord_399161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399196 : List Nat := [2, 2, 4, 2, 2, 8]
def baseStart_399196 : Nat := 118140960795 + 399196 * 2 ^ 59
def prefixEnd_399196 : Nat := 4983230072969 + 3 ^ 40 * 399196 * 2
def baseEnd_399196 : Nat := 6748293772916061811165

theorem tailTrace_399196 : CollatzResearch.WordTrace tailWord_399196 prefixEnd_399196 6748293772916061811165 := by
  unfold tailWord_399196
  simp only [CollatzResearch.WordTrace]
  refine ⟨7279937130894272047020721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9706582841192362729360961 7279937130894272047020721)
  ·
    refine ⟨5459952848170704035265541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7279937130894272047020721 5459952848170704035265541)
    ·
      refine ⟨1023741159032007006612289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5459952848170704035265541 1023741159032007006612289)
      ·
        refine ⟨767805869274005254959217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1023741159032007006612289 767805869274005254959217)
        ·
          refine ⟨575854401955503941219413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767805869274005254959217 575854401955503941219413)
          ·
            refine ⟨6748293772916061811165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 575854401955503941219413 6748293772916061811165)
            ·
              rfl

theorem cell20_399196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 8].length) (baseStart_399196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399196 prefixEnd_399196 := by exact prefixLift 399196
  have htrace : WordTrace (prefixWord ++ tailWord_399196) baseStart_399196 baseEnd_399196 := by
    simpa [prefixWord, tailWord_399196, baseEnd_399196] using wordTrace_append hprefix tailTrace_399196
  have hstable : (prefixWord ++ tailWord_399196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399196).length < 2 ^ (prefixWord ++ tailWord_399196).sum := by decide
  have hdescent : baseEnd_399196 < baseStart_399196 := by decide
  rcases family_descends (prefixWord ++ tailWord_399196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399202 : List Nat := [3, 3, 2, 1, 2, 3, 2, 2, 2]
def baseStart_399202 : Nat := 118140960795 + 399202 * 2 ^ 59
def prefixEnd_399202 : Nat := 4983230072969 + 3 ^ 40 * 399202 * 2
def baseEnd_399202 : Nat := 182206670432224314701431

theorem tailTrace_399202 : CollatzResearch.WordTrace tailWord_399202 prefixEnd_399202 182206670432224314701431 := by
  unfold tailWord_399202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3640023274941701779689965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9706728733177871412506573 3640023274941701779689965)
  ·
    refine ⟨1365008728103138167383737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3640023274941701779689965 1365008728103138167383737)
    ·
      refine ⟨1023756546077353625537803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1365008728103138167383737 1023756546077353625537803)
      ·
        refine ⟨1535634819116030438306705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1023756546077353625537803 1535634819116030438306705)
        ·
          refine ⟨1151726114337022828730029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1535634819116030438306705 1151726114337022828730029)
          ·
            refine ⟨431897292876383560773761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1151726114337022828730029 431897292876383560773761)
            ·
              refine ⟨323922969657287670580321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431897292876383560773761 323922969657287670580321)
              ·
                refine ⟨242942227242965752935241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323922969657287670580321 242942227242965752935241)
                ·
                  refine ⟨182206670432224314701431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 242942227242965752935241 182206670432224314701431)
                  ·
                    rfl

theorem cell20_399202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_399202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399202 prefixEnd_399202 := by exact prefixLift 399202
  have htrace : WordTrace (prefixWord ++ tailWord_399202) baseStart_399202 baseEnd_399202 := by
    simpa [prefixWord, tailWord_399202, baseEnd_399202] using wordTrace_append hprefix tailTrace_399202
  have hstable : (prefixWord ++ tailWord_399202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399202).length < 2 ^ (prefixWord ++ tailWord_399202).sum := by decide
  have hdescent : baseEnd_399202 < baseStart_399202 := by decide
  rcases family_descends (prefixWord ++ tailWord_399202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399230 : List Nat := [4, 2, 3, 1, 1, 2, 3, 4]
def baseStart_399230 : Nat := 118140960795 + 399230 * 2 ^ 59
def prefixEnd_399230 : Nat := 4983230072969 + 3 ^ 40 * 399230 * 2
def baseEnd_399230 : Nat := 60739816798393553922661

theorem tailTrace_399230 : CollatzResearch.WordTrace tailWord_399230 prefixEnd_399230 60739816798393553922661 := by
  unfold tailWord_399230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1820139292958170987597393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9707409562443578600519429 1820139292958170987597393)
  ·
    refine ⟨1365104469718628240698045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1820139292958170987597393 1365104469718628240698045)
    ·
      refine ⟨511914176144485590261767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1365104469718628240698045 511914176144485590261767)
      ·
        refine ⟨767871264216728385392651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511914176144485590261767 767871264216728385392651)
        ·
          refine ⟨1151806896325092578088977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 767871264216728385392651 1151806896325092578088977)
          ·
            refine ⟨863855172243819433566733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1151806896325092578088977 863855172243819433566733)
            ·
              refine ⟨323945689591432287587525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 863855172243819433566733 323945689591432287587525)
              ·
                refine ⟨60739816798393553922661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 323945689591432287587525 60739816798393553922661)
                ·
                  rfl

theorem cell20_399230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_399230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399230 prefixEnd_399230 := by exact prefixLift 399230
  have htrace : WordTrace (prefixWord ++ tailWord_399230) baseStart_399230 baseEnd_399230 := by
    simpa [prefixWord, tailWord_399230, baseEnd_399230] using wordTrace_append hprefix tailTrace_399230
  have hstable : (prefixWord ++ tailWord_399230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399230).length < 2 ^ (prefixWord ++ tailWord_399230).sum := by decide
  have hdescent : baseEnd_399230 < baseStart_399230 := by decide
  rcases family_descends (prefixWord ++ tailWord_399230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399254 : List Nat := [5, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_399254 : Nat := 118140960795 + 399254 * 2 ^ 59
def prefixEnd_399254 : Nat := 4983230072969 + 3 ^ 40 * 399254 * 2
def baseEnd_399254 : Nat := 182230404649143244967885

theorem tailTrace_399254 : CollatzResearch.WordTrace tailWord_399254 prefixEnd_399254 182230404649143244967885 := by
  unfold tailWord_399254
  simp only [CollatzResearch.WordTrace]
  refine ⟨910124355973651249978301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9707993130385613333101877 910124355973651249978301)
  ·
    refine ⟨341296633490119218741863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 910124355973651249978301 341296633490119218741863)
    ·
      refine ⟨511944950235178828112795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341296633490119218741863 511944950235178828112795)
      ·
        refine ⟨767917425352768242169193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511944950235178828112795 767917425352768242169193)
        ·
          refine ⟨575938069014576181626895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767917425352768242169193 575938069014576181626895)
          ·
            refine ⟨863907103521864272440343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575938069014576181626895 863907103521864272440343)
            ·
              refine ⟨1295860655282796408660515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863907103521864272440343 1295860655282796408660515)
              ·
                refine ⟨1943790982924194612990773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1295860655282796408660515 1943790982924194612990773)
                ·
                  refine ⟨182230404649143244967885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1943790982924194612990773 182230404649143244967885)
                  ·
                    rfl

theorem cell20_399254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_399254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399254 prefixEnd_399254 := by exact prefixLift 399254
  have htrace : WordTrace (prefixWord ++ tailWord_399254) baseStart_399254 baseEnd_399254 := by
    simpa [prefixWord, tailWord_399254, baseEnd_399254] using wordTrace_append hprefix tailTrace_399254
  have hstable : (prefixWord ++ tailWord_399254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399254).length < 2 ^ (prefixWord ++ tailWord_399254).sum := by decide
  have hdescent : baseEnd_399254 < baseStart_399254 := by decide
  rcases family_descends (prefixWord ++ tailWord_399254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399255 : List Nat := [1, 1, 3, 3, 1, 4, 7]
def baseStart_399255 : Nat := 118140960795 + 399255 * 2 ^ 59
def prefixEnd_399255 : Nat := 4983230072969 + 3 ^ 40 * 399255 * 2
def baseEnd_399255 : Nat := 20247873452932409548283

theorem tailTrace_399255 : CollatzResearch.WordTrace tailWord_399255 prefixEnd_399255 20247873452932409548283 := by
  unfold tailWord_399255
  simp only [CollatzResearch.WordTrace]
  refine ⟨14562026168574797170439219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9708017445716531446959479 14562026168574797170439219)
  ·
    refine ⟨21843039252862195755658829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14562026168574797170439219 21843039252862195755658829)
    ·
      refine ⟨8191139719823323408372061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21843039252862195755658829 8191139719823323408372061)
      ·
        refine ⟨3071677394933746278139523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8191139719823323408372061 3071677394933746278139523)
        ·
          refine ⟨4607516092400619417209285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3071677394933746278139523 4607516092400619417209285)
          ·
            refine ⟨863909267325116140726741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4607516092400619417209285 863909267325116140726741)
            ·
              refine ⟨20247873452932409548283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 863909267325116140726741 20247873452932409548283)
              ·
                rfl

theorem cell20_399255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 7].length) (baseStart_399255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399255 prefixEnd_399255 := by exact prefixLift 399255
  have htrace : WordTrace (prefixWord ++ tailWord_399255) baseStart_399255 baseEnd_399255 := by
    simpa [prefixWord, tailWord_399255, baseEnd_399255] using wordTrace_append hprefix tailTrace_399255
  have hstable : (prefixWord ++ tailWord_399255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399255).length < 2 ^ (prefixWord ++ tailWord_399255).sum := by decide
  have hdescent : baseEnd_399255 < baseStart_399255 := by decide
  rcases family_descends (prefixWord ++ tailWord_399255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399258 : List Nat := [3, 1, 1, 4, 2, 1, 3, 2, 3]
def baseStart_399258 : Nat := 118140960795 + 399258 * 2 ^ 59
def prefixEnd_399258 : Nat := 4983230072969 + 3 ^ 40 * 399258 * 2
def baseEnd_399258 : Nat := 182232230358137008834535

theorem tailTrace_399258 : CollatzResearch.WordTrace tailWord_399258 prefixEnd_399258 182232230358137008834535 := by
  unfold tailWord_399258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3640533896890982170699607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9708090391709285788532285 3640533896890982170699607)
  ·
    refine ⟨5460800845336473256049411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3640533896890982170699607 5460800845336473256049411)
    ·
      refine ⟨8191201268004709884074117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5460800845336473256049411 8191201268004709884074117)
      ·
        refine ⟨1535850237750883103263897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8191201268004709884074117 1535850237750883103263897)
        ·
          refine ⟨1151887678313162327447923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1535850237750883103263897 1151887678313162327447923)
          ·
            refine ⟨1727831517469743491171885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1151887678313162327447923 1727831517469743491171885)
            ·
              refine ⟨647936819051153809189457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1727831517469743491171885 647936819051153809189457)
              ·
                refine ⟨485952614288365356892093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 647936819051153809189457 485952614288365356892093)
                ·
                  refine ⟨182232230358137008834535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485952614288365356892093 182232230358137008834535)
                  ·
                    rfl

theorem cell20_399258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_399258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399258 prefixEnd_399258 := by exact prefixLift 399258
  have htrace : WordTrace (prefixWord ++ tailWord_399258) baseStart_399258 baseEnd_399258 := by
    simpa [prefixWord, tailWord_399258, baseEnd_399258] using wordTrace_append hprefix tailTrace_399258
  have hstable : (prefixWord ++ tailWord_399258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399258).length < 2 ^ (prefixWord ++ tailWord_399258).sum := by decide
  have hdescent : baseEnd_399258 < baseStart_399258 := by decide
  rcases family_descends (prefixWord ++ tailWord_399258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399317 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 5]
def baseStart_399317 : Nat := 118140960795 + 399317 * 2 ^ 59
def prefixEnd_399317 : Nat := 4983230072969 + 3 ^ 40 * 399317 * 2
def baseEnd_399317 : Nat := 182259159565795025867627

theorem tailTrace_399317 : CollatzResearch.WordTrace tailWord_399317 prefixEnd_399317 182259159565795025867627 := by
  unfold tailWord_399317
  simp only [CollatzResearch.WordTrace]
  refine ⟨14564287494350181759196205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9709524996233454506130803 14564287494350181759196205)
  ·
    refine ⟨5461607810381318159698577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14564287494350181759196205 5461607810381318159698577)
    ·
      refine ⟨4096205857785988619773933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5461607810381318159698577 4096205857785988619773933)
      ·
        refine ⟨1536077196669745732415225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4096205857785988619773933 1536077196669745732415225)
        ·
          refine ⟨1152057897502309299311419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1536077196669745732415225 1152057897502309299311419)
          ·
            refine ⟨1728086846253463948967129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152057897502309299311419 1728086846253463948967129)
            ·
              refine ⟨1296065134690097961725347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1728086846253463948967129 1296065134690097961725347)
              ·
                refine ⟨1944097702035146942588021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296065134690097961725347 1944097702035146942588021)
                ·
                  refine ⟨182259159565795025867627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1944097702035146942588021 182259159565795025867627)
                  ·
                    rfl

theorem cell20_399317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_399317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399317 prefixEnd_399317 := by exact prefixLift 399317
  have htrace : WordTrace (prefixWord ++ tailWord_399317) baseStart_399317 baseEnd_399317 := by
    simpa [prefixWord, tailWord_399317, baseEnd_399317] using wordTrace_append hprefix tailTrace_399317
  have hstable : (prefixWord ++ tailWord_399317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399317).length < 2 ^ (prefixWord ++ tailWord_399317).sum := by decide
  have hdescent : baseEnd_399317 < baseStart_399317 := by decide
  rcases family_descends (prefixWord ++ tailWord_399317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399320 : List Nat := [2, 1, 2, 2, 2, 2, 5, 2, 2]
def baseStart_399320 : Nat := 118140960795 + 399320 * 2 ^ 59
def prefixEnd_399320 : Nat := 4983230072969 + 3 ^ 40 * 399320 * 2
def baseEnd_399320 : Nat := 182260528847540348767615

theorem tailTrace_399320 : CollatzResearch.WordTrace tailWord_399320 prefixEnd_399320 182260528847540348767615 := by
  unfold tailWord_399320
  simp only [CollatzResearch.WordTrace]
  refine ⟨7282198456669656635777707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9709597942226208847703609 7282198456669656635777707)
  ·
    refine ⟨10923297685004484953666561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7282198456669656635777707 10923297685004484953666561)
    ·
      refine ⟨8192473263753363715249921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10923297685004484953666561 8192473263753363715249921)
      ·
        refine ⟨6144354947815022786437441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8192473263753363715249921 6144354947815022786437441)
        ·
          refine ⟨4608266210861267089828081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6144354947815022786437441 4608266210861267089828081)
          ·
            refine ⟨3456199658145950317371061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4608266210861267089828081 3456199658145950317371061)
            ·
              refine ⟨324018717951182842253537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3456199658145950317371061 324018717951182842253537)
              ·
                refine ⟨243014038463387131690153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324018717951182842253537 243014038463387131690153)
                ·
                  refine ⟨182260528847540348767615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243014038463387131690153 182260528847540348767615)
                  ·
                    rfl

theorem cell20_399320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 2].length) (baseStart_399320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399320 prefixEnd_399320 := by exact prefixLift 399320
  have htrace : WordTrace (prefixWord ++ tailWord_399320) baseStart_399320 baseEnd_399320 := by
    simpa [prefixWord, tailWord_399320, baseEnd_399320] using wordTrace_append hprefix tailTrace_399320
  have hstable : (prefixWord ++ tailWord_399320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399320).length < 2 ^ (prefixWord ++ tailWord_399320).sum := by decide
  have hdescent : baseEnd_399320 < baseStart_399320 := by decide
  rcases family_descends (prefixWord ++ tailWord_399320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399331 : List Nat := [1, 1, 1, 6, 1, 2, 1, 7]
def baseStart_399331 : Nat := 118140960795 + 399331 * 2 ^ 59
def prefixEnd_399331 : Nat := 4983230072969 + 3 ^ 40 * 399331 * 2
def baseEnd_399331 : Nat := 60755183182424399800301

theorem tailTrace_399331 : CollatzResearch.WordTrace tailWord_399331 prefixEnd_399331 60755183182424399800301 := by
  unfold tailWord_399331
  simp only [CollatzResearch.WordTrace]
  refine ⟨14564798116299462150205847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9709865410866308100137231 14564798116299462150205847)
  ·
    refine ⟨21847197174449193225308771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14564798116299462150205847 21847197174449193225308771)
    ·
      refine ⟨32770795761673789837963157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21847197174449193225308771 32770795761673789837963157)
      ·
        refine ⟨1536131051328458898654523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32770795761673789837963157 1536131051328458898654523)
        ·
          refine ⟨2304196576992688347981785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1536131051328458898654523 2304196576992688347981785)
          ·
            refine ⟨1728147432744516260986339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2304196576992688347981785 1728147432744516260986339)
            ·
              refine ⟨2592221149116774391479509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1728147432744516260986339 2592221149116774391479509)
              ·
                refine ⟨60755183182424399800301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2592221149116774391479509 60755183182424399800301)
                ·
                  rfl

theorem cell20_399331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 7].length) (baseStart_399331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399331 prefixEnd_399331 := by exact prefixLift 399331
  have htrace : WordTrace (prefixWord ++ tailWord_399331) baseStart_399331 baseEnd_399331 := by
    simpa [prefixWord, tailWord_399331, baseEnd_399331] using wordTrace_append hprefix tailTrace_399331
  have hstable : (prefixWord ++ tailWord_399331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399331).length < 2 ^ (prefixWord ++ tailWord_399331).sum := by decide
  have hdescent : baseEnd_399331 < baseStart_399331 := by decide
  rcases family_descends (prefixWord ++ tailWord_399331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399386 : List Nat := [3, 1, 1, 3, 1, 5, 1, 5]
def baseStart_399386 : Nat := 118140960795 + 399386 * 2 ^ 59
def prefixEnd_399386 : Nat := 4983230072969 + 3 ^ 40 * 399386 * 2
def baseEnd_399386 : Nat := 60763551015312484189115

theorem tailTrace_399386 : CollatzResearch.WordTrace tailWord_399386 prefixEnd_399386 60763551015312484189115 := by
  unfold tailWord_399386
  simp only [CollatzResearch.WordTrace]
  refine ⟨3641701032775051635864503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9711202754066804362305341 3641701032775051635864503)
  ·
    refine ⟨5462551549162577453796755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3641701032775051635864503 5462551549162577453796755)
    ·
      refine ⟨8193827323743866180695133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5462551549162577453796755 8193827323743866180695133)
      ·
        refine ⟨3072685246403949817760675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8193827323743866180695133 3072685246403949817760675)
        ·
          refine ⟨4609027869605924726641013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3072685246403949817760675 4609027869605924726641013)
          ·
            refine ⟨432096362775555443122595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4609027869605924726641013 432096362775555443122595)
            ·
              refine ⟨648144544163333164683893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432096362775555443122595 648144544163333164683893)
              ·
                refine ⟨60763551015312484189115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 648144544163333164683893 60763551015312484189115)
                ·
                  rfl

theorem cell20_399386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_399386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399386 prefixEnd_399386 := by exact prefixLift 399386
  have htrace : WordTrace (prefixWord ++ tailWord_399386) baseStart_399386 baseEnd_399386 := by
    simpa [prefixWord, tailWord_399386, baseEnd_399386] using wordTrace_append hprefix tailTrace_399386
  have hstable : (prefixWord ++ tailWord_399386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399386).length < 2 ^ (prefixWord ++ tailWord_399386).sum := by decide
  have hdescent : baseEnd_399386 < baseStart_399386 := by decide
  rcases family_descends (prefixWord ++ tailWord_399386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399438 : List Nat := [4, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_399438 : Nat := 118140960795 + 399438 * 2 ^ 59
def prefixEnd_399438 : Nat := 4983230072969 + 3 ^ 40 * 399438 * 2
def baseEnd_399438 : Nat := 182314387262856382833799

theorem tailTrace_399438 : CollatzResearch.WordTrace tailWord_399438 prefixEnd_399438 182314387262856382833799 := by
  unfold tailWord_399438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1821087590863977428043871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9712467151274546282900645 1821087590863977428043871)
  ·
    refine ⟨2731631386295966142065807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1821087590863977428043871 2731631386295966142065807)
    ·
      refine ⟨4097447079443949213098711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2731631386295966142065807 4097447079443949213098711)
      ·
        refine ⟨6146170619165923819648067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4097447079443949213098711 6146170619165923819648067)
        ·
          refine ⟨9219255928748885729472101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6146170619165923819648067 9219255928748885729472101)
          ·
            refine ⟨1728610486640416074276019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9219255928748885729472101 1728610486640416074276019)
            ·
              refine ⟨2592915729960624111414029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1728610486640416074276019 2592915729960624111414029)
              ·
                refine ⟨972343398735234041780261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2592915729960624111414029 972343398735234041780261)
                ·
                  refine ⟨182314387262856382833799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 972343398735234041780261 182314387262856382833799)
                  ·
                    rfl

theorem cell20_399438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_399438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399438 prefixEnd_399438 := by exact prefixLift 399438
  have htrace : WordTrace (prefixWord ++ tailWord_399438) baseStart_399438 baseEnd_399438 := by
    simpa [prefixWord, tailWord_399438, baseEnd_399438] using wordTrace_append hprefix tailTrace_399438
  have hstable : (prefixWord ++ tailWord_399438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399438).length < 2 ^ (prefixWord ++ tailWord_399438).sum := by decide
  have hdescent : baseEnd_399438 < baseStart_399438 := by decide
  rcases family_descends (prefixWord ++ tailWord_399438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399448 : List Nat := [2, 1, 2, 2, 1, 5, 3, 1, 3]
def baseStart_399448 : Nat := 118140960795 + 399448 * 2 ^ 59
def prefixEnd_399448 : Nat := 4983230072969 + 3 ^ 40 * 399448 * 2
def baseEnd_399448 : Nat := 182318951535340792500425

theorem tailTrace_399448 : CollatzResearch.WordTrace tailWord_399448 prefixEnd_399448 182318951535340792500425 := by
  unfold tailWord_399448
  simp only [CollatzResearch.WordTrace]
  refine ⟨7284532728437795566107499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9712710304583727421476665 7284532728437795566107499)
  ·
    refine ⟨10926799092656693349161249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7284532728437795566107499 10926799092656693349161249)
    ·
      refine ⟨8195099319492520011870937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10926799092656693349161249 8195099319492520011870937)
      ·
        refine ⟨6146324489619390008903203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8195099319492520011870937 6146324489619390008903203)
        ·
          refine ⟨9219486734429085013354805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6146324489619390008903203 9219486734429085013354805)
          ·
            refine ⟨864326881352726720002013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9219486734429085013354805 864326881352726720002013)
            ·
              refine ⟨324122580507272520000755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 864326881352726720002013 324122580507272520000755)
              ·
                refine ⟨486183870760908780001133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324122580507272520000755 486183870760908780001133)
                ·
                  refine ⟨182318951535340792500425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486183870760908780001133 182318951535340792500425)
                  ·
                    rfl

theorem cell20_399448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 3].length) (baseStart_399448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399448 prefixEnd_399448 := by exact prefixLift 399448
  have htrace : WordTrace (prefixWord ++ tailWord_399448) baseStart_399448 baseEnd_399448 := by
    simpa [prefixWord, tailWord_399448, baseEnd_399448] using wordTrace_append hprefix tailTrace_399448
  have hstable : (prefixWord ++ tailWord_399448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399448).length < 2 ^ (prefixWord ++ tailWord_399448).sum := by decide
  have hdescent : baseEnd_399448 < baseStart_399448 := by decide
  rcases family_descends (prefixWord ++ tailWord_399448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399454 : List Nat := [4, 4, 1, 1, 3, 1, 2, 4]
def baseStart_399454 : Nat := 118140960795 + 399454 * 2 ^ 59
def prefixEnd_399454 : Nat := 4983230072969 + 3 ^ 40 * 399454 * 2
def baseEnd_399454 : Nat := 60773896699610479433467

theorem tailTrace_399454 : CollatzResearch.WordTrace tailWord_399454 prefixEnd_399454 60773896699610479433467 := by
  unfold tailWord_399454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1821160536856731769616677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9712856196569236104622277 1821160536856731769616677)
  ·
    refine ⟨341467600660637206803127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1821160536856731769616677 341467600660637206803127)
    ·
      refine ⟨512201400990955810204691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 341467600660637206803127 512201400990955810204691)
      ·
        refine ⟨768302101486433715307037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 512201400990955810204691 768302101486433715307037)
        ·
          refine ⟨288113288057412643240139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 768302101486433715307037 288113288057412643240139)
          ·
            refine ⟨432169932086118964860209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288113288057412643240139 432169932086118964860209)
            ·
              refine ⟨324127449064589223645157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432169932086118964860209 324127449064589223645157)
              ·
                refine ⟨60773896699610479433467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324127449064589223645157 60773896699610479433467)
                ·
                  rfl

theorem cell20_399454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_399454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399454 prefixEnd_399454 := by exact prefixLift 399454
  have htrace : WordTrace (prefixWord ++ tailWord_399454) baseStart_399454 baseEnd_399454 := by
    simpa [prefixWord, tailWord_399454, baseEnd_399454] using wordTrace_append hprefix tailTrace_399454
  have hstable : (prefixWord ++ tailWord_399454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399454).length < 2 ^ (prefixWord ++ tailWord_399454).sum := by decide
  have hdescent : baseEnd_399454 < baseStart_399454 := by decide
  rcases family_descends (prefixWord ++ tailWord_399454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399458 : List Nat := [3, 3, 2, 2, 2, 2, 2, 4]
def baseStart_399458 : Nat := 118140960795 + 399458 * 2 ^ 59
def prefixEnd_399458 : Nat := 4983230072969 + 3 ^ 40 * 399458 * 2
def baseEnd_399458 : Nat := 60774505269275067389017

theorem tailTrace_399458 : CollatzResearch.WordTrace tailWord_399458 prefixEnd_399458 60774505269275067389017 := by
  unfold tailWord_399458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3642357546709840710019757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9712953457892908560052685 3642357546709840710019757)
  ·
    refine ⟨1365884080016190266257409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3642357546709840710019757 1365884080016190266257409)
    ·
      refine ⟨1024413060012142699693057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1365884080016190266257409 1024413060012142699693057)
      ·
        refine ⟨768309795009107024769793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1024413060012142699693057 768309795009107024769793)
        ·
          refine ⟨576232346256830268577345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 768309795009107024769793 576232346256830268577345)
          ·
            refine ⟨432174259692622701433009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576232346256830268577345 432174259692622701433009)
            ·
              refine ⟨324130694769467026074757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432174259692622701433009 324130694769467026074757)
              ·
                refine ⟨60774505269275067389017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324130694769467026074757 60774505269275067389017)
                ·
                  rfl

theorem cell20_399458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_399458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399458 prefixEnd_399458 := by exact prefixLift 399458
  have htrace : WordTrace (prefixWord ++ tailWord_399458) baseStart_399458 baseEnd_399458 := by
    simpa [prefixWord, tailWord_399458, baseEnd_399458] using wordTrace_append hprefix tailTrace_399458
  have hstable : (prefixWord ++ tailWord_399458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399458).length < 2 ^ (prefixWord ++ tailWord_399458).sum := by decide
  have hdescent : baseEnd_399458 < baseStart_399458 := by decide
  rcases family_descends (prefixWord ++ tailWord_399458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399472 : List Nat := [2, 1, 1, 1, 5, 4, 1, 3, 2]
def baseStart_399472 : Nat := 118140960795 + 399472 * 2 ^ 59
def prefixEnd_399472 : Nat := 4983230072969 + 3 ^ 40 * 399472 * 2
def baseEnd_399472 : Nat := 182329905789303375700327

theorem tailTrace_399472 : CollatzResearch.WordTrace tailWord_399472 prefixEnd_399472 182329905789303375700327 := by
  unfold tailWord_399472
  simp only [CollatzResearch.WordTrace]
  refine ⟨7284970404394321615544335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9713293872525762154059113 7284970404394321615544335)
  ·
    refine ⟨10927455606591482423316503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7284970404394321615544335 10927455606591482423316503)
    ·
      refine ⟨16391183409887223634974755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10927455606591482423316503 16391183409887223634974755)
      ·
        refine ⟨24586775114830835452462133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16391183409887223634974755 24586775114830835452462133)
        ·
          refine ⟨2305010167015390823668325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24586775114830835452462133 2305010167015390823668325)
          ·
            refine ⟨432189406315385779437811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2305010167015390823668325 432189406315385779437811)
            ·
              refine ⟨648284109473078669156717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432189406315385779437811 648284109473078669156717)
              ·
                refine ⟨243106541052404500933769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 648284109473078669156717 243106541052404500933769)
                ·
                  refine ⟨182329905789303375700327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243106541052404500933769 182329905789303375700327)
                  ·
                    rfl

theorem cell20_399472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 2].length) (baseStart_399472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399472 prefixEnd_399472 := by exact prefixLift 399472
  have htrace : WordTrace (prefixWord ++ tailWord_399472) baseStart_399472 baseEnd_399472 := by
    simpa [prefixWord, tailWord_399472, baseEnd_399472] using wordTrace_append hprefix tailTrace_399472
  have hstable : (prefixWord ++ tailWord_399472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399472).length < 2 ^ (prefixWord ++ tailWord_399472).sum := by decide
  have hdescent : baseEnd_399472 < baseStart_399472 := by decide
  rcases family_descends (prefixWord ++ tailWord_399472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399489 : List Nat := [1, 2, 4, 2, 3, 1, 3, 2, 2]
def baseStart_399489 : Nat := 118140960795 + 399489 * 2 ^ 59
def prefixEnd_399489 : Nat := 4983230072969 + 3 ^ 40 * 399489 * 2
def baseEnd_399489 : Nat := 182337665052526872133591

theorem tailTrace_399489 : CollatzResearch.WordTrace tailWord_399489 prefixEnd_399489 182337665052526872133591 := by
  unfold tailWord_399489
  simp only [CollatzResearch.WordTrace]
  refine ⟨14570560849727055134457521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9713707233151370089638347 14570560849727055134457521)
  ·
    refine ⟨10927920637295291350843141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14570560849727055134457521 10927920637295291350843141)
    ·
      refine ⟨2048985119492867128283089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10927920637295291350843141 2048985119492867128283089)
      ·
        refine ⟨1536738839619650346212317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2048985119492867128283089 1536738839619650346212317)
        ·
          refine ⟨576277064857368879829619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1536738839619650346212317 576277064857368879829619)
          ·
            refine ⟨864415597286053319744429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576277064857368879829619 864415597286053319744429)
            ·
              refine ⟨324155848982269994904161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 864415597286053319744429 324155848982269994904161)
              ·
                refine ⟨243116886736702496178121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324155848982269994904161 243116886736702496178121)
                ·
                  refine ⟨182337665052526872133591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243116886736702496178121 182337665052526872133591)
                  ·
                    rfl

theorem cell20_399489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 2, 2].length) (baseStart_399489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399489 prefixEnd_399489 := by exact prefixLift 399489
  have htrace : WordTrace (prefixWord ++ tailWord_399489) baseStart_399489 baseEnd_399489 := by
    simpa [prefixWord, tailWord_399489, baseEnd_399489] using wordTrace_append hprefix tailTrace_399489
  have hstable : (prefixWord ++ tailWord_399489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399489).length < 2 ^ (prefixWord ++ tailWord_399489).sum := by decide
  have hdescent : baseEnd_399489 < baseStart_399489 := by decide
  rcases family_descends (prefixWord ++ tailWord_399489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399493 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 4]
def baseStart_399493 : Nat := 118140960795 + 399493 * 2 ^ 59
def prefixEnd_399493 : Nat := 4983230072969 + 3 ^ 40 * 399493 * 2
def baseEnd_399493 : Nat := 182339490761520636000241

theorem tailTrace_399493 : CollatzResearch.WordTrace tailWord_399493 prefixEnd_399493 182339490761520636000241 := by
  unfold tailWord_399493
  simp only [CollatzResearch.WordTrace]
  refine ⟨14570706741712563817603133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9713804494475042545068755 14570706741712563817603133)
  ·
    refine ⟨5464015028142211431601175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14570706741712563817603133 5464015028142211431601175)
    ·
      refine ⟨8196022542213317147401763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5464015028142211431601175 8196022542213317147401763)
      ·
        refine ⟨12294033813319975721102645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8196022542213317147401763 12294033813319975721102645)
        ·
          refine ⟨1152565669998747723853373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12294033813319975721102645 1152565669998747723853373)
          ·
            refine ⟨432212126249530396445015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1152565669998747723853373 432212126249530396445015)
            ·
              refine ⟨648318189374295594667523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432212126249530396445015 648318189374295594667523)
              ·
                refine ⟨972477284061443392001285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 648318189374295594667523 972477284061443392001285)
                ·
                  refine ⟨182339490761520636000241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 972477284061443392001285 182339490761520636000241)
                  ·
                    rfl

theorem cell20_399493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_399493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399493 prefixEnd_399493 := by exact prefixLift 399493
  have htrace : WordTrace (prefixWord ++ tailWord_399493) baseStart_399493 baseEnd_399493 := by
    simpa [prefixWord, tailWord_399493, baseEnd_399493] using wordTrace_append hprefix tailTrace_399493
  have hstable : (prefixWord ++ tailWord_399493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399493).length < 2 ^ (prefixWord ++ tailWord_399493).sum := by decide
  have hdescent : baseEnd_399493 < baseStart_399493 := by decide
  rcases family_descends (prefixWord ++ tailWord_399493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399521 : List Nat := [1, 2, 3, 3, 1, 2, 2, 6]
def baseStart_399521 : Nat := 118140960795 + 399521 * 2 ^ 59
def prefixEnd_399521 : Nat := 4983230072969 + 3 ^ 40 * 399521 * 2
def baseEnd_399521 : Nat := 60784090241492327688931

theorem tailTrace_399521 : CollatzResearch.WordTrace tailWord_399521 prefixEnd_399521 60784090241492327688931 := by
  unfold tailWord_399521
  simp only [CollatzResearch.WordTrace]
  refine ⟨14571727985611124599622417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9714485323740749733081611 14571727985611124599622417)
  ·
    refine ⟨10928795989208343449716813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14571727985611124599622417 10928795989208343449716813)
    ·
      refine ⟨4098298495953128793643805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10928795989208343449716813 4098298495953128793643805)
      ·
        refine ⟨1536861935982423297616427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4098298495953128793643805 1536861935982423297616427)
        ·
          refine ⟨2305292903973634946424641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1536861935982423297616427 2305292903973634946424641)
          ·
            refine ⟨1728969677980226209818481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2305292903973634946424641 1728969677980226209818481)
            ·
              refine ⟨1296727258485169657363861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1728969677980226209818481 1296727258485169657363861)
              ·
                refine ⟨60784090241492327688931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1296727258485169657363861 60784090241492327688931)
                ·
                  rfl

theorem cell20_399521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 6].length) (baseStart_399521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399521 prefixEnd_399521 := by exact prefixLift 399521
  have htrace : WordTrace (prefixWord ++ tailWord_399521) baseStart_399521 baseEnd_399521 := by
    simpa [prefixWord, tailWord_399521, baseEnd_399521] using wordTrace_append hprefix tailTrace_399521
  have hstable : (prefixWord ++ tailWord_399521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399521).length < 2 ^ (prefixWord ++ tailWord_399521).sum := by decide
  have hdescent : baseEnd_399521 < baseStart_399521 := by decide
  rcases family_descends (prefixWord ++ tailWord_399521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399540 : List Nat := [2, 5, 3, 1, 1, 2, 2, 2, 2]
def baseStart_399540 : Nat := 118140960795 + 399540 * 2 ^ 59
def prefixEnd_399540 : Nat := 4983230072969 + 3 ^ 40 * 399540 * 2
def baseEnd_399540 : Nat := 182360942842197361433383

theorem tailTrace_399540 : CollatzResearch.WordTrace tailWord_399540 prefixEnd_399540 182360942842197361433383 := by
  unfold tailWord_399540
  simp only [CollatzResearch.WordTrace]
  refine ⟨7286210486271145422282037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9714947315028193896376049 7286210486271145422282037)
  ·
    refine ⟨683082233087919883338941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7286210486271145422282037 683082233087919883338941)
    ·
      refine ⟨256155837407969956252103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 683082233087919883338941 256155837407969956252103)
      ·
        refine ⟨384233756111954934378155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256155837407969956252103 384233756111954934378155)
        ·
          refine ⟨576350634167932401567233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384233756111954934378155 576350634167932401567233)
          ·
            refine ⟨432262975625949301175425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576350634167932401567233 432262975625949301175425)
            ·
              refine ⟨324197231719461975881569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432262975625949301175425 324197231719461975881569)
              ·
                refine ⟨243147923789596481911177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324197231719461975881569 243147923789596481911177)
                ·
                  refine ⟨182360942842197361433383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243147923789596481911177 182360942842197361433383)
                  ·
                    rfl

theorem cell20_399540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_399540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399540 prefixEnd_399540 := by exact prefixLift 399540
  have htrace : WordTrace (prefixWord ++ tailWord_399540) baseStart_399540 baseEnd_399540 := by
    simpa [prefixWord, tailWord_399540, baseEnd_399540] using wordTrace_append hprefix tailTrace_399540
  have hstable : (prefixWord ++ tailWord_399540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399540).length < 2 ^ (prefixWord ++ tailWord_399540).sum := by decide
  have hdescent : baseEnd_399540 < baseStart_399540 := by decide
  rcases family_descends (prefixWord ++ tailWord_399540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399541 : List Nat := [1, 3, 3, 4, 1, 1, 2, 2, 3]
def baseStart_399541 : Nat := 118140960795 + 399541 * 2 ^ 59
def prefixEnd_399541 : Nat := 4983230072969 + 3 ^ 40 * 399541 * 2
def baseEnd_399541 : Nat := 182361399269445802400045

theorem tailTrace_399541 : CollatzResearch.WordTrace tailWord_399541 prefixEnd_399541 182361399269445802400045 := by
  unfold tailWord_399541
  simp only [CollatzResearch.WordTrace]
  refine ⟨14572457445538668015350477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9714971630359112010233651 14572457445538668015350477)
  ·
    refine ⟨5464671542077000505756429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14572457445538668015350477 5464671542077000505756429)
    ·
      refine ⟨2049251828278875189658661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5464671542077000505756429 2049251828278875189658661)
      ·
        refine ⟨384234717802289098060999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2049251828278875189658661 384234717802289098060999)
        ·
          refine ⟨576352076703433647091499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384234717802289098060999 576352076703433647091499)
          ·
            refine ⟨864528115055150470637249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576352076703433647091499 864528115055150470637249)
            ·
              refine ⟨648396086291362852977937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 864528115055150470637249 648396086291362852977937)
              ·
                refine ⟨486297064718522139733453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648396086291362852977937 486297064718522139733453)
                ·
                  refine ⟨182361399269445802400045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486297064718522139733453 182361399269445802400045)
                  ·
                    rfl

theorem cell20_399541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_399541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399541 prefixEnd_399541 := by exact prefixLift 399541
  have htrace : WordTrace (prefixWord ++ tailWord_399541) baseStart_399541 baseEnd_399541 := by
    simpa [prefixWord, tailWord_399541, baseEnd_399541] using wordTrace_append hprefix tailTrace_399541
  have hstable : (prefixWord ++ tailWord_399541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399541).length < 2 ^ (prefixWord ++ tailWord_399541).sum := by decide
  have hdescent : baseEnd_399541 < baseStart_399541 := by decide
  rcases family_descends (prefixWord ++ tailWord_399541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399545 : List Nat := [1, 2, 1, 4, 1, 2, 4, 2, 3]
def baseStart_399545 : Nat := 118140960795 + 399545 * 2 ^ 59
def prefixEnd_399545 : Nat := 4983230072969 + 3 ^ 40 * 399545 * 2
def baseEnd_399545 : Nat := 182363224978439566266695

theorem tailTrace_399545 : CollatzResearch.WordTrace tailWord_399545 prefixEnd_399545 182363224978439566266695 := by
  unfold tailWord_399545
  simp only [CollatzResearch.WordTrace]
  refine ⟨14572603337524176698496089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9715068891682784465664059 14572603337524176698496089)
  ·
    refine ⟨10929452503143132523872067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14572603337524176698496089 10929452503143132523872067)
    ·
      refine ⟨16394178754714698785808101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10929452503143132523872067 16394178754714698785808101)
      ·
        refine ⟨3073908516509006022339019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16394178754714698785808101 3073908516509006022339019)
        ·
          refine ⟨4610862774763509033508529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3073908516509006022339019 4610862774763509033508529)
          ·
            refine ⟨3458147081072631775131397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4610862774763509033508529 3458147081072631775131397)
            ·
              refine ⟨648402577701118457837137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3458147081072631775131397 648402577701118457837137)
              ·
                refine ⟨486301933275838843377853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648402577701118457837137 486301933275838843377853)
                ·
                  refine ⟨182363224978439566266695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486301933275838843377853 182363224978439566266695)
                  ·
                    rfl

theorem cell20_399545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 3].length) (baseStart_399545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399545 prefixEnd_399545 := by exact prefixLift 399545
  have htrace : WordTrace (prefixWord ++ tailWord_399545) baseStart_399545 baseEnd_399545 := by
    simpa [prefixWord, tailWord_399545, baseEnd_399545] using wordTrace_append hprefix tailTrace_399545
  have hstable : (prefixWord ++ tailWord_399545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399545).length < 2 ^ (prefixWord ++ tailWord_399545).sum := by decide
  have hdescent : baseEnd_399545 < baseStart_399545 := by decide
  rcases family_descends (prefixWord ++ tailWord_399545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399548 : List Nat := [2, 2, 2, 3, 3, 1, 1, 4, 2]
def baseStart_399548 : Nat := 118140960795 + 399548 * 2 ^ 59
def prefixEnd_399548 : Nat := 4983230072969 + 3 ^ 40 * 399548 * 2
def baseEnd_399548 : Nat := 182364594260184889166683

theorem tailTrace_399548 : CollatzResearch.WordTrace tailWord_399548 prefixEnd_399548 182364594260184889166683 := by
  unfold tailWord_399548
  simp only [CollatzResearch.WordTrace]
  refine ⟨7286356378256654105427649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9715141837675538807236865 7286356378256654105427649)
  ·
    refine ⟨5464767283692490579070737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7286356378256654105427649 5464767283692490579070737)
    ·
      refine ⟨4098575462769367934303053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5464767283692490579070737 4098575462769367934303053)
      ·
        refine ⟨1536965798538512975363645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4098575462769367934303053 1536965798538512975363645)
        ·
          refine ⟨576362174451942365761367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1536965798538512975363645 576362174451942365761367)
          ·
            refine ⟨864543261677913548642051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576362174451942365761367 864543261677913548642051)
            ·
              refine ⟨1296814892516870322963077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864543261677913548642051 1296814892516870322963077)
              ·
                refine ⟨243152792346913185555577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1296814892516870322963077 243152792346913185555577)
                ·
                  refine ⟨182364594260184889166683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243152792346913185555577 182364594260184889166683)
                  ·
                    rfl

theorem cell20_399548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_399548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399548 prefixEnd_399548 := by exact prefixLift 399548
  have htrace : WordTrace (prefixWord ++ tailWord_399548) baseStart_399548 baseEnd_399548 := by
    simpa [prefixWord, tailWord_399548, baseEnd_399548] using wordTrace_append hprefix tailTrace_399548
  have hstable : (prefixWord ++ tailWord_399548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399548).length < 2 ^ (prefixWord ++ tailWord_399548).sum := by decide
  have hdescent : baseEnd_399548 < baseStart_399548 := by decide
  rcases family_descends (prefixWord ++ tailWord_399548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399576 : List Nat := [2, 1, 2, 2, 4, 2, 3, 4]
def baseStart_399576 : Nat := 118140960795 + 399576 * 2 ^ 59
def prefixEnd_399576 : Nat := 4983230072969 + 3 ^ 40 * 399576 * 2
def baseEnd_399576 : Nat := 60792458074380412077745

theorem tailTrace_399576 : CollatzResearch.WordTrace tailWord_399576 prefixEnd_399576 60792458074380412077745 := by
  unfold tailWord_399576
  simp only [CollatzResearch.WordTrace]
  refine ⟨7286867000205934496437291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9715822666941245995249721 7286867000205934496437291)
  ·
    refine ⟨10930300500308901744655937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7286867000205934496437291 10930300500308901744655937)
    ·
      refine ⟨8197725375231676308491953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10930300500308901744655937 8197725375231676308491953)
      ·
        refine ⟨6148294031423757231368965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8197725375231676308491953 6148294031423757231368965)
        ·
          refine ⟨1152805130891954480881681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6148294031423757231368965 1152805130891954480881681)
          ·
            refine ⟨864603848168965860661261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1152805130891954480881681 864603848168965860661261)
            ·
              refine ⟨324226443063362197747973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 864603848168965860661261 324226443063362197747973)
              ·
                refine ⟨60792458074380412077745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324226443063362197747973 60792458074380412077745)
                ·
                  rfl

theorem cell20_399576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_399576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399576 prefixEnd_399576 := by exact prefixLift 399576
  have htrace : WordTrace (prefixWord ++ tailWord_399576) baseStart_399576 baseEnd_399576 := by
    simpa [prefixWord, tailWord_399576, baseEnd_399576] using wordTrace_append hprefix tailTrace_399576
  have hstable : (prefixWord ++ tailWord_399576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399576).length < 2 ^ (prefixWord ++ tailWord_399576).sum := by decide
  have hdescent : baseEnd_399576 < baseStart_399576 := by decide
  rcases family_descends (prefixWord ++ tailWord_399576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399649 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 6]
def baseStart_399649 : Nat := 118140960795 + 399649 * 2 ^ 59
def prefixEnd_399649 : Nat := 4983230072969 + 3 ^ 40 * 399649 * 2
def baseEnd_399649 : Nat := 182410693412277426799603

theorem tailTrace_399649 : CollatzResearch.WordTrace tailWord_399649 prefixEnd_399649 182410693412277426799603 := by
  unfold tailWord_399649
  simp only [CollatzResearch.WordTrace]
  refine ⟨14576396529147402460282001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9717597686098268306854667 14576396529147402460282001)
  ·
    refine ⟨10932297396860551845211501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14576396529147402460282001 10932297396860551845211501)
    ·
      refine ⟨4099611523822706941954313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10932297396860551845211501 4099611523822706941954313)
      ·
        refine ⟨3074708642867030206465735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4099611523822706941954313 3074708642867030206465735)
        ·
          refine ⟨4612062964300545309698603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3074708642867030206465735 4612062964300545309698603)
          ·
            refine ⟨6918094446450817964547905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4612062964300545309698603 6918094446450817964547905)
            ·
              refine ⟨5188570834838113473410929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6918094446450817964547905 5188570834838113473410929)
              ·
                refine ⟨3891428126128585105058197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5188570834838113473410929 3891428126128585105058197)
                ·
                  refine ⟨182410693412277426799603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3891428126128585105058197 182410693412277426799603)
                  ·
                    rfl

theorem cell20_399649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_399649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399649 prefixEnd_399649 := by exact prefixLift 399649
  have htrace : WordTrace (prefixWord ++ tailWord_399649) baseStart_399649 baseEnd_399649 := by
    simpa [prefixWord, tailWord_399649, baseEnd_399649] using wordTrace_append hprefix tailTrace_399649
  have hstable : (prefixWord ++ tailWord_399649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399649).length < 2 ^ (prefixWord ++ tailWord_399649).sum := by decide
  have hdescent : baseEnd_399649 < baseStart_399649 := by decide
  rcases family_descends (prefixWord ++ tailWord_399649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399673 : List Nat := [1, 2, 1, 6, 1, 1, 1, 7]
def baseStart_399673 : Nat := 118140960795 + 399673 * 2 ^ 59
def prefixEnd_399673 : Nat := 4983230072969 + 3 ^ 40 * 399673 * 2
def baseEnd_399673 : Nat := 60807215888746669999835

theorem tailTrace_399673 : CollatzResearch.WordTrace tailWord_399673 prefixEnd_399673 60807215888746669999835 := by
  unfold tailWord_399673
  simp only [CollatzResearch.WordTrace]
  refine ⟨14577271881060454559155673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9718181254040303039437115 14577271881060454559155673)
  ·
    refine ⟨10932953910795340919366755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14577271881060454559155673 10932953910795340919366755)
    ·
      refine ⟨16399430866193011379050133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10932953910795340919366755 16399430866193011379050133)
      ·
        refine ⟨768723321852797408392975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16399430866193011379050133 768723321852797408392975)
        ·
          refine ⟨1153084982779196112589463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768723321852797408392975 1153084982779196112589463)
          ·
            refine ⟨1729627474168794168884195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153084982779196112589463 1729627474168794168884195)
            ·
              refine ⟨2594441211253191253326293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729627474168794168884195 2594441211253191253326293)
              ·
                refine ⟨60807215888746669999835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2594441211253191253326293 60807215888746669999835)
                ·
                  rfl

theorem cell20_399673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 7].length) (baseStart_399673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399673 prefixEnd_399673 := by exact prefixLift 399673
  have htrace : WordTrace (prefixWord ++ tailWord_399673) baseStart_399673 baseEnd_399673 := by
    simpa [prefixWord, tailWord_399673, baseEnd_399673] using wordTrace_append hprefix tailTrace_399673
  have hstable : (prefixWord ++ tailWord_399673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399673).length < 2 ^ (prefixWord ++ tailWord_399673).sum := by decide
  have hdescent : baseEnd_399673 < baseStart_399673 := by decide
  rcases family_descends (prefixWord ++ tailWord_399673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399687 : List Nat := [1, 1, 4, 1, 2, 2, 2, 1, 6]
def baseStart_399687 : Nat := 118140960795 + 399687 * 2 ^ 59
def prefixEnd_399687 : Nat := 4983230072969 + 3 ^ 40 * 399687 * 2
def baseEnd_399687 : Nat := 182428037647718183532781

theorem tailTrace_399687 : CollatzResearch.WordTrace tailWord_399687 prefixEnd_399687 182428037647718183532781 := by
  unfold tailWord_399687
  simp only [CollatzResearch.WordTrace]
  refine ⟨14577782503009734950165315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9718521668673156633443543 14577782503009734950165315)
  ·
    refine ⟨21866673754514602425247973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14577782503009734950165315 21866673754514602425247973)
    ·
      refine ⟨4100001328971487954733995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21866673754514602425247973 4100001328971487954733995)
      ·
        refine ⟨6150001993457231932100993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100001328971487954733995 6150001993457231932100993)
        ·
          refine ⟨4612501495092923949075745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6150001993457231932100993 4612501495092923949075745)
          ·
            refine ⟨3459376121319692961806809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4612501495092923949075745 3459376121319692961806809)
            ·
              refine ⟨2594532090989769721355107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3459376121319692961806809 2594532090989769721355107)
              ·
                refine ⟨3891798136484654582032661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2594532090989769721355107 3891798136484654582032661)
                ·
                  refine ⟨182428037647718183532781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3891798136484654582032661 182428037647718183532781)
                  ·
                    rfl

theorem cell20_399687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_399687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399687 prefixEnd_399687 := by exact prefixLift 399687
  have htrace : WordTrace (prefixWord ++ tailWord_399687) baseStart_399687 baseEnd_399687 := by
    simpa [prefixWord, tailWord_399687, baseEnd_399687] using wordTrace_append hprefix tailTrace_399687
  have hstable : (prefixWord ++ tailWord_399687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399687).length < 2 ^ (prefixWord ++ tailWord_399687).sum := by decide
  have hdescent : baseEnd_399687 < baseStart_399687 := by decide
  rcases family_descends (prefixWord ++ tailWord_399687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399714 : List Nat := [3, 3, 2, 1, 1, 3, 2, 2, 3]
def baseStart_399714 : Nat := 118140960795 + 399714 * 2 ^ 59
def prefixEnd_399714 : Nat := 4983230072969 + 3 ^ 40 * 399714 * 2
def baseEnd_399714 : Nat := 182440361183426089632671

theorem tailTrace_399714 : CollatzResearch.WordTrace tailWord_399714 prefixEnd_399714 182440361183426089632671 := by
  unfold tailWord_399714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3644691818477979640349549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9719178182607945707598797 3644691818477979640349549)
  ·
    refine ⟨1366759431929242365131081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3644691818477979640349549 1366759431929242365131081)
    ·
      refine ⟨1025069573946931773848311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1366759431929242365131081 1025069573946931773848311)
      ·
        refine ⟨1537604360920397660772467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025069573946931773848311 1537604360920397660772467)
        ·
          refine ⟨2306406541380596491158701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537604360920397660772467 2306406541380596491158701)
          ·
            refine ⟨864902453017723684184513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2306406541380596491158701 864902453017723684184513)
            ·
              refine ⟨648676839763292763138385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 864902453017723684184513 648676839763292763138385)
              ·
                refine ⟨486507629822469572353789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 648676839763292763138385 486507629822469572353789)
                ·
                  refine ⟨182440361183426089632671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486507629822469572353789 182440361183426089632671)
                  ·
                    rfl

theorem cell20_399714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_399714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399714 prefixEnd_399714 := by exact prefixLift 399714
  have htrace : WordTrace (prefixWord ++ tailWord_399714) baseStart_399714 baseEnd_399714 := by
    simpa [prefixWord, tailWord_399714, baseEnd_399714] using wordTrace_append hprefix tailTrace_399714
  have hstable : (prefixWord ++ tailWord_399714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399714).length < 2 ^ (prefixWord ++ tailWord_399714).sum := by decide
  have hdescent : baseEnd_399714 < baseStart_399714 := by decide
  rcases family_descends (prefixWord ++ tailWord_399714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399773 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 5]
def baseStart_399773 : Nat := 118140960795 + 399773 * 2 ^ 59
def prefixEnd_399773 : Nat := 4983230072969 + 3 ^ 40 * 399773 * 2
def baseEnd_399773 : Nat := 182467290391084106665763

theorem tailTrace_399773 : CollatzResearch.WordTrace tailWord_399773 prefixEnd_399773 182467290391084106665763 := by
  unfold tailWord_399773
  simp only [CollatzResearch.WordTrace]
  refine ⟨14580919180698171637795973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9720612787132114425197315 14580919180698171637795973)
  ·
    refine ⟨2733922346380907182086745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14580919180698171637795973 2733922346380907182086745)
    ·
      refine ⟨2050441759785680386565059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2733922346380907182086745 2050441759785680386565059)
      ·
        refine ⟨3075662639678520579847589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2050441759785680386565059 3075662639678520579847589)
        ·
          refine ⟨576686744939722608721423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3075662639678520579847589 576686744939722608721423)
          ·
            refine ⟨865030117409583913082135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 576686744939722608721423 865030117409583913082135)
            ·
              refine ⟨1297545176114375869623203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865030117409583913082135 1297545176114375869623203)
              ·
                refine ⟨1946317764171563804434805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1297545176114375869623203 1946317764171563804434805)
                ·
                  refine ⟨182467290391084106665763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1946317764171563804434805 182467290391084106665763)
                  ·
                    rfl

theorem cell20_399773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_399773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399773 prefixEnd_399773 := by exact prefixLift 399773
  have htrace : WordTrace (prefixWord ++ tailWord_399773) baseStart_399773 baseEnd_399773 := by
    simpa [prefixWord, tailWord_399773, baseEnd_399773] using wordTrace_append hprefix tailTrace_399773
  have hstable : (prefixWord ++ tailWord_399773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399773).length < 2 ^ (prefixWord ++ tailWord_399773).sum := by decide
  have hdescent : baseEnd_399773 < baseStart_399773 := by decide
  rcases family_descends (prefixWord ++ tailWord_399773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399804 : List Nat := [2, 2, 2, 4, 1, 1, 4, 4]
def baseStart_399804 : Nat := 118140960795 + 399804 * 2 ^ 59
def prefixEnd_399804 : Nat := 4983230072969 + 3 ^ 40 * 399804 * 2
def baseEnd_399804 : Nat := 60827146545261925544101

theorem tailTrace_399804 : CollatzResearch.WordTrace tailWord_399804 prefixEnd_399804 60827146545261925544101 := by
  unfold tailWord_399804
  simp only [CollatzResearch.WordTrace]
  refine ⟨7291024921792931966087233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9721366562390575954782977 7291024921792931966087233)
  ·
    refine ⟨5468268691344698974565425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7291024921792931966087233 5468268691344698974565425)
    ·
      refine ⟨4101201518508524230924069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5468268691344698974565425 4101201518508524230924069)
      ·
        refine ⟨768975284720348293298263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4101201518508524230924069 768975284720348293298263)
        ·
          refine ⟨1153462927080522439947395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 768975284720348293298263 1153462927080522439947395)
          ·
            refine ⟨1730194390620783659921093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153462927080522439947395 1730194390620783659921093)
            ·
              refine ⟨324411448241396936235205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1730194390620783659921093 324411448241396936235205)
              ·
                refine ⟨60827146545261925544101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324411448241396936235205 60827146545261925544101)
                ·
                  rfl

theorem cell20_399804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_399804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399804 prefixEnd_399804 := by exact prefixLift 399804
  have htrace : WordTrace (prefixWord ++ tailWord_399804) baseStart_399804 baseEnd_399804 := by
    simpa [prefixWord, tailWord_399804, baseEnd_399804] using wordTrace_append hprefix tailTrace_399804
  have hstable : (prefixWord ++ tailWord_399804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399804).length < 2 ^ (prefixWord ++ tailWord_399804).sum := by decide
  have hdescent : baseEnd_399804 < baseStart_399804 := by decide
  rcases family_descends (prefixWord ++ tailWord_399804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399832 : List Nat := [2, 1, 2, 2, 2, 1, 1, 6, 3]
def baseStart_399832 : Nat := 118140960795 + 399832 * 2 ^ 59
def prefixEnd_399832 : Nat := 4983230072969 + 3 ^ 40 * 399832 * 2
def baseEnd_399832 : Nat := 182494219598742123698855

theorem tailTrace_399832 : CollatzResearch.WordTrace tailWord_399832 prefixEnd_399832 182494219598742123698855 := by
  unfold tailWord_399832
  simp only [CollatzResearch.WordTrace]
  refine ⟨7291535543742212357096875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9722047391656283142795833 7291535543742212357096875)
  ·
    refine ⟨10937303315613318535645313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7291535543742212357096875 10937303315613318535645313)
    ·
      refine ⟨8202977486709988901733985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10937303315613318535645313 8202977486709988901733985)
      ·
        refine ⟨6152233115032491676300489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8202977486709988901733985 6152233115032491676300489)
        ·
          refine ⟨4614174836274368757225367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6152233115032491676300489 4614174836274368757225367)
          ·
            refine ⟨6921262254411553135838051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4614174836274368757225367 6921262254411553135838051)
            ·
              refine ⟨10381893381617329703757077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6921262254411553135838051 10381893381617329703757077)
              ·
                refine ⟨486651252263312329863613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10381893381617329703757077 486651252263312329863613)
                ·
                  refine ⟨182494219598742123698855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486651252263312329863613 182494219598742123698855)
                  ·
                    rfl

theorem cell20_399832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_399832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399832 prefixEnd_399832 := by exact prefixLift 399832
  have htrace : WordTrace (prefixWord ++ tailWord_399832) baseStart_399832 baseEnd_399832 := by
    simpa [prefixWord, tailWord_399832, baseEnd_399832] using wordTrace_append hprefix tailTrace_399832
  have hstable : (prefixWord ++ tailWord_399832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399832).length < 2 ^ (prefixWord ++ tailWord_399832).sum := by decide
  have hdescent : baseEnd_399832 < baseStart_399832 := by decide
  rcases family_descends (prefixWord ++ tailWord_399832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399845 : List Nat := [1, 3, 1, 5, 2, 2, 2, 1, 3]
def baseStart_399845 : Nat := 118140960795 + 399845 * 2 ^ 59
def prefixEnd_399845 : Nat := 4983230072969 + 3 ^ 40 * 399845 * 2
def baseEnd_399845 : Nat := 182500153152971856265469

theorem tailTrace_399845 : CollatzResearch.WordTrace tailWord_399845 prefixEnd_399845 182500153152971856265469 := by
  unfold tailWord_399845
  simp only [CollatzResearch.WordTrace]
  refine ⟨14583545236437327934416989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9722363490958218622944659 14583545236437327934416989)
  ·
    refine ⟨5468829463663997975406371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14583545236437327934416989 5468829463663997975406371)
    ·
      refine ⟨8203244195495996963109557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5468829463663997975406371 8203244195495996963109557)
      ·
        refine ⟨769054143327749715291521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8203244195495996963109557 769054143327749715291521)
        ·
          refine ⟨576790607495812286468641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 769054143327749715291521 576790607495812286468641)
          ·
            refine ⟨432592955621859214851481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 576790607495812286468641 432592955621859214851481)
            ·
              refine ⟨324444716716394411138611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432592955621859214851481 324444716716394411138611)
              ·
                refine ⟨486667075074591616707917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324444716716394411138611 486667075074591616707917)
                ·
                  refine ⟨182500153152971856265469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486667075074591616707917 182500153152971856265469)
                  ·
                    rfl

theorem cell20_399845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_399845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399845 prefixEnd_399845 := by exact prefixLift 399845
  have htrace : WordTrace (prefixWord ++ tailWord_399845) baseStart_399845 baseEnd_399845 := by
    simpa [prefixWord, tailWord_399845, baseEnd_399845] using wordTrace_append hprefix tailTrace_399845
  have hstable : (prefixWord ++ tailWord_399845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399845).length < 2 ^ (prefixWord ++ tailWord_399845).sum := by decide
  have hdescent : baseEnd_399845 < baseStart_399845 := by decide
  rcases family_descends (prefixWord ++ tailWord_399845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399884 : List Nat := [2, 2, 1, 2, 4, 9]
def baseStart_399884 : Nat := 118140960795 + 399884 * 2 ^ 59
def prefixEnd_399884 : Nat := 4983230072969 + 3 ^ 40 * 399884 * 2
def baseEnd_399884 : Nat := 6759924215394853850567

theorem tailTrace_399884 : CollatzResearch.WordTrace tailWord_399884 prefixEnd_399884 6759924215394853850567 := by
  unfold tailWord_399884
  simp only [CollatzResearch.WordTrace]
  refine ⟨7292483841648018797543353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9723311788864025063391137 7292483841648018797543353)
  ·
    refine ⟨5469362881236014098157515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7292483841648018797543353 5469362881236014098157515)
    ·
      refine ⟨8204044321854021147236273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5469362881236014098157515 8204044321854021147236273)
      ·
        refine ⟨6153033241390515860427205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8204044321854021147236273 6153033241390515860427205)
        ·
          refine ⟨1153693732760721723830101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6153033241390515860427205 1153693732760721723830101)
          ·
            refine ⟨6759924215394853850567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1153693732760721723830101 6759924215394853850567)
            ·
              rfl

theorem cell20_399884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 9].length) (baseStart_399884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399884 prefixEnd_399884 := by exact prefixLift 399884
  have htrace : WordTrace (prefixWord ++ tailWord_399884) baseStart_399884 baseEnd_399884 := by
    simpa [prefixWord, tailWord_399884, baseEnd_399884] using wordTrace_append hprefix tailTrace_399884
  have hstable : (prefixWord ++ tailWord_399884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399884).length < 2 ^ (prefixWord ++ tailWord_399884).sum := by decide
  have hdescent : baseEnd_399884 < baseStart_399884 := by decide
  rcases family_descends (prefixWord ++ tailWord_399884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399901 : List Nat := [1, 4, 2, 2, 1, 2, 3, 5]
def baseStart_399901 : Nat := 118140960795 + 399901 * 2 ^ 59
def prefixEnd_399901 : Nat := 4983230072969 + 3 ^ 40 * 399901 * 2
def baseEnd_399901 : Nat := 60841904359628183466191

theorem tailTrace_399901 : CollatzResearch.WordTrace tailWord_399901 prefixEnd_399901 60841904359628183466191 := by
  unfold tailWord_399901
  simp only [CollatzResearch.WordTrace]
  refine ⟨14585587724234449498455557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9723725149489632998970371 14585587724234449498455557)
  ·
    refine ⟨2734797698293959280960417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14585587724234449498455557 2734797698293959280960417)
    ·
      refine ⟨2051098273720469460720313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2734797698293959280960417 2051098273720469460720313)
      ·
        refine ⟨1538323705290352095540235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2051098273720469460720313 1538323705290352095540235)
        ·
          refine ⟨2307485557935528143310353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538323705290352095540235 2307485557935528143310353)
          ·
            refine ⟨1730614168451646107482765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2307485557935528143310353 1730614168451646107482765)
            ·
              refine ⟨648980313169367290306037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1730614168451646107482765 648980313169367290306037)
              ·
                refine ⟨60841904359628183466191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 648980313169367290306037 60841904359628183466191)
                ·
                  rfl

theorem cell20_399901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 5].length) (baseStart_399901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399901 prefixEnd_399901 := by exact prefixLift 399901
  have htrace : WordTrace (prefixWord ++ tailWord_399901) baseStart_399901 baseEnd_399901 := by
    simpa [prefixWord, tailWord_399901, baseEnd_399901] using wordTrace_append hprefix tailTrace_399901
  have hstable : (prefixWord ++ tailWord_399901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399901).length < 2 ^ (prefixWord ++ tailWord_399901).sum := by decide
  have hdescent : baseEnd_399901 < baseStart_399901 := by decide
  rcases family_descends (prefixWord ++ tailWord_399901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399922 : List Nat := [3, 2, 1, 1, 2, 1, 2, 8]
def baseStart_399922 : Nat := 118140960795 + 399922 * 2 ^ 59
def prefixEnd_399922 : Nat := 4983230072969 + 3 ^ 40 * 399922 * 2
def baseEnd_399922 : Nat := 60845099350367270232829

theorem tailTrace_399922 : CollatzResearch.WordTrace tailWord_399922 prefixEnd_399922 60845099350367270232829 := by
  unfold tailWord_399922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3646588414289592521242505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9724235771438913389980013 3646588414289592521242505)
  ·
    refine ⟨2734941310717194390931879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3646588414289592521242505 2734941310717194390931879)
    ·
      refine ⟨4102411966075791586397819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2734941310717194390931879 4102411966075791586397819)
      ·
        refine ⟨6153617949113687379596729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4102411966075791586397819 6153617949113687379596729)
        ·
          refine ⟨4615213461835265534697547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6153617949113687379596729 4615213461835265534697547)
          ·
            refine ⟨6922820192752898302046321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4615213461835265534697547 6922820192752898302046321)
            ·
              refine ⟨5192115144564673726534741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6922820192752898302046321 5192115144564673726534741)
              ·
                refine ⟨60845099350367270232829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5192115144564673726534741 60845099350367270232829)
                ·
                  rfl

theorem cell20_399922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_399922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399922 prefixEnd_399922 := by exact prefixLift 399922
  have htrace : WordTrace (prefixWord ++ tailWord_399922) baseStart_399922 baseEnd_399922 := by
    simpa [prefixWord, tailWord_399922, baseEnd_399922] using wordTrace_append hprefix tailTrace_399922
  have hstable : (prefixWord ++ tailWord_399922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399922).length < 2 ^ (prefixWord ++ tailWord_399922).sum := by decide
  have hdescent : baseEnd_399922 < baseStart_399922 := by decide
  rcases family_descends (prefixWord ++ tailWord_399922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399942 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_399942 : Nat := 118140960795 + 399942 * 2 ^ 59
def prefixEnd_399942 : Nat := 4983230072969 + 3 ^ 40 * 399942 * 2
def baseEnd_399942 : Nat := 182544426596070630031739

theorem tailTrace_399942 : CollatzResearch.WordTrace tailWord_399942 prefixEnd_399942 182544426596070630031739 := by
  unfold tailWord_399942
  simp only [CollatzResearch.WordTrace]
  refine ⟨455846347408934796896815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9724722078057275667132053 455846347408934796896815)
  ·
    refine ⟨683769521113402195345223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 455846347408934796896815 683769521113402195345223)
    ·
      refine ⟨1025654281670103293017835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 683769521113402195345223 1025654281670103293017835)
      ·
        refine ⟨1538481422505154939526753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025654281670103293017835 1538481422505154939526753)
        ·
          refine ⟨1153861066878866204645065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1538481422505154939526753 1153861066878866204645065)
          ·
            refine ⟨865395800159149653483799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1153861066878866204645065 865395800159149653483799)
            ·
              refine ⟨1298093700238724480225699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865395800159149653483799 1298093700238724480225699)
              ·
                refine ⟨1947140550358086720338549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298093700238724480225699 1947140550358086720338549)
                ·
                  refine ⟨182544426596070630031739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1947140550358086720338549 182544426596070630031739)
                  ·
                    rfl

theorem cell20_399942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_399942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399942 prefixEnd_399942 := by exact prefixLift 399942
  have htrace : WordTrace (prefixWord ++ tailWord_399942) baseStart_399942 baseEnd_399942 := by
    simpa [prefixWord, tailWord_399942, baseEnd_399942] using wordTrace_append hprefix tailTrace_399942
  have hstable : (prefixWord ++ tailWord_399942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399942).length < 2 ^ (prefixWord ++ tailWord_399942).sum := by decide
  have hdescent : baseEnd_399942 < baseStart_399942 := by decide
  rcases family_descends (prefixWord ++ tailWord_399942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399946 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_399946 : Nat := 118140960795 + 399946 * 2 ^ 59
def prefixEnd_399946 : Nat := 4983230072969 + 3 ^ 40 * 399946 * 2
def baseEnd_399946 : Nat := 182546252305064393898389

theorem tailTrace_399946 : CollatzResearch.WordTrace tailWord_399946 prefixEnd_399946 182546252305064393898389 := by
  unfold tailWord_399946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3646807252267855545960923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9724819339380948122562461 3646807252267855545960923)
  ·
    refine ⟨5470210878401783318941385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3646807252267855545960923 5470210878401783318941385)
    ·
      refine ⟨4102658158801337489206039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5470210878401783318941385 4102658158801337489206039)
      ·
        refine ⟨6153987238202006233809059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4102658158801337489206039 6153987238202006233809059)
        ·
          refine ⟨9230980857303009350713589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6153987238202006233809059 9230980857303009350713589)
          ·
            refine ⟨865404455372157126629399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9230980857303009350713589 865404455372157126629399)
            ·
              refine ⟨1298106683058235689944099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865404455372157126629399 1298106683058235689944099)
              ·
                refine ⟨1947160024587353534916149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298106683058235689944099 1947160024587353534916149)
                ·
                  refine ⟨182546252305064393898389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1947160024587353534916149 182546252305064393898389)
                  ·
                    rfl

theorem cell20_399946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_399946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399946 prefixEnd_399946 := by exact prefixLift 399946
  have htrace : WordTrace (prefixWord ++ tailWord_399946) baseStart_399946 baseEnd_399946 := by
    simpa [prefixWord, tailWord_399946, baseEnd_399946] using wordTrace_append hprefix tailTrace_399946
  have hstable : (prefixWord ++ tailWord_399946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399946).length < 2 ^ (prefixWord ++ tailWord_399946).sum := by decide
  have hdescent : baseEnd_399946 < baseStart_399946 := by decide
  rcases family_descends (prefixWord ++ tailWord_399946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399949 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 4]
def baseStart_399949 : Nat := 118140960795 + 399949 * 2 ^ 59
def prefixEnd_399949 : Nat := 4983230072969 + 3 ^ 40 * 399949 * 2
def baseEnd_399949 : Nat := 182547621586809716798377

theorem tailTrace_399949 : CollatzResearch.WordTrace tailWord_399949 prefixEnd_399949 182547621586809716798377 := by
  unfold tailWord_399949
  simp only [CollatzResearch.WordTrace]
  refine ⟨14587338428060553696202901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9724892285373702464135267 14587338428060553696202901)
  ·
    refine ⟨683781488815338454509511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14587338428060553696202901 683781488815338454509511)
    ·
      refine ⟨1025672233223007681764267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 683781488815338454509511 1025672233223007681764267)
      ·
        refine ⟨1538508349834511522646401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025672233223007681764267 1538508349834511522646401)
        ·
          refine ⟨1153881262375883641984801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1538508349834511522646401 1153881262375883641984801)
          ·
            refine ⟨865410946781912731488601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1153881262375883641984801 865410946781912731488601)
            ·
              refine ⟨649058210086434548616451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865410946781912731488601 649058210086434548616451)
              ·
                refine ⟨973587315129651822924677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649058210086434548616451 973587315129651822924677)
                ·
                  refine ⟨182547621586809716798377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 973587315129651822924677 182547621586809716798377)
                  ·
                    rfl

theorem cell20_399949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_399949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399949 prefixEnd_399949 := by exact prefixLift 399949
  have htrace : WordTrace (prefixWord ++ tailWord_399949) baseStart_399949 baseEnd_399949 := by
    simpa [prefixWord, tailWord_399949, baseEnd_399949] using wordTrace_append hprefix tailTrace_399949
  have hstable : (prefixWord ++ tailWord_399949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399949).length < 2 ^ (prefixWord ++ tailWord_399949).sum := by decide
  have hdescent : baseEnd_399949 < baseStart_399949 := by decide
  rcases family_descends (prefixWord ++ tailWord_399949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399953 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 4]
def baseStart_399953 : Nat := 118140960795 + 399953 * 2 ^ 59
def prefixEnd_399953 : Nat := 4983230072969 + 3 ^ 40 * 399953 * 2
def baseEnd_399953 : Nat := 182549447295803480665027

theorem tailTrace_399953 : CollatzResearch.WordTrace tailWord_399953 prefixEnd_399953 182549447295803480665027 := by
  unfold tailWord_399953
  simp only [CollatzResearch.WordTrace]
  refine ⟨14587484320046062379348513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9724989546697374919565675 14587484320046062379348513)
  ·
    refine ⟨10940613240034546784511385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14587484320046062379348513 10940613240034546784511385)
    ·
      refine ⟨8205459930025910088383539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10940613240034546784511385 8205459930025910088383539)
      ·
        refine ⟨12308189895038865132575309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8205459930025910088383539 12308189895038865132575309)
        ·
          refine ⟨4615571210639574424715741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12308189895038865132575309 4615571210639574424715741)
          ·
            refine ⟨1730839203989840409268403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4615571210639574424715741 1730839203989840409268403)
            ·
              refine ⟨2596258805984760613902605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730839203989840409268403 2596258805984760613902605)
              ·
                refine ⟨973597052244285230213477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2596258805984760613902605 973597052244285230213477)
                ·
                  refine ⟨182549447295803480665027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 973597052244285230213477 182549447295803480665027)
                  ·
                    rfl

theorem cell20_399953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_399953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399953 prefixEnd_399953 := by exact prefixLift 399953
  have htrace : WordTrace (prefixWord ++ tailWord_399953) baseStart_399953 baseEnd_399953 := by
    simpa [prefixWord, tailWord_399953, baseEnd_399953] using wordTrace_append hprefix tailTrace_399953
  have hstable : (prefixWord ++ tailWord_399953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399953).length < 2 ^ (prefixWord ++ tailWord_399953).sum := by decide
  have hdescent : baseEnd_399953 < baseStart_399953 := by decide
  rcases family_descends (prefixWord ++ tailWord_399953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_399973 : List Nat := [1, 3, 1, 3, 5, 1, 2, 4]
def baseStart_399973 : Nat := 118140960795 + 399973 * 2 ^ 59
def prefixEnd_399973 : Nat := 4983230072969 + 3 ^ 40 * 399973 * 2
def baseEnd_399973 : Nat := 60852858613590766666093

theorem tailTrace_399973 : CollatzResearch.WordTrace tailWord_399973 prefixEnd_399973 60852858613590766666093 := by
  unfold tailWord_399973
  simp only [CollatzResearch.WordTrace]
  refine ⟨14588213779973605795076573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9725475853315737196717715 14588213779973605795076573)
  ·
    refine ⟨5470580167490102173153715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14588213779973605795076573 5470580167490102173153715)
    ·
      refine ⟨8205870251235153259730573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5470580167490102173153715 8205870251235153259730573)
      ·
        refine ⟨3077201344213182472398965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8205870251235153259730573 3077201344213182472398965)
        ·
          refine ⟨288487626019985856787403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3077201344213182472398965 288487626019985856787403)
          ·
            refine ⟨432731439029978785181105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288487626019985856787403 432731439029978785181105)
            ·
              refine ⟨324548579272484088885829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 432731439029978785181105 324548579272484088885829)
              ·
                refine ⟨60852858613590766666093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324548579272484088885829 60852858613590766666093)
                ·
                  rfl

theorem cell20_399973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 4].length) (baseStart_399973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_399973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_399973 prefixEnd_399973 := by exact prefixLift 399973
  have htrace : WordTrace (prefixWord ++ tailWord_399973) baseStart_399973 baseEnd_399973 := by
    simpa [prefixWord, tailWord_399973, baseEnd_399973] using wordTrace_append hprefix tailTrace_399973
  have hstable : (prefixWord ++ tailWord_399973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_399973).length < 2 ^ (prefixWord ++ tailWord_399973).sum := by decide
  have hdescent : baseEnd_399973 < baseStart_399973 := by decide
  rcases family_descends (prefixWord ++ tailWord_399973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400004 : List Nat := [2, 3, 2, 1, 3, 2, 3, 2, 2]
def baseStart_400004 : Nat := 118140960795 + 400004 * 2 ^ 59
def prefixEnd_400004 : Nat := 4983230072969 + 3 ^ 40 * 400004 * 2
def baseEnd_400004 : Nat := 182572725085473969964819

theorem tailTrace_400004 : CollatzResearch.WordTrace tailWord_400004 prefixEnd_400004 182572725085473969964819 := by
  unfold tailWord_400004
  simp only [CollatzResearch.WordTrace]
  refine ⟨7294672221430649044727533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9726229628574198726303377 7294672221430649044727533)
  ·
    refine ⟨2735502083036493391772825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7294672221430649044727533 2735502083036493391772825)
    ·
      refine ⟨2051626562277370043829619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2735502083036493391772825 2051626562277370043829619)
      ·
        refine ⟨3077439843416055065744429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2051626562277370043829619 3077439843416055065744429)
        ·
          refine ⟨1154039941281020649654161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3077439843416055065744429 1154039941281020649654161)
          ·
            refine ⟨865529955960765487240621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1154039941281020649654161 865529955960765487240621)
            ·
              refine ⟨324573733485287057715233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 865529955960765487240621 324573733485287057715233)
              ·
                refine ⟨243430300113965293286425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324573733485287057715233 243430300113965293286425)
                ·
                  refine ⟨182572725085473969964819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243430300113965293286425 182572725085473969964819)
                  ·
                    rfl

theorem cell20_400004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_400004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400004 prefixEnd_400004 := by exact prefixLift 400004
  have htrace : WordTrace (prefixWord ++ tailWord_400004) baseStart_400004 baseEnd_400004 := by
    simpa [prefixWord, tailWord_400004, baseEnd_400004] using wordTrace_append hprefix tailTrace_400004
  have hstable : (prefixWord ++ tailWord_400004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400004).length < 2 ^ (prefixWord ++ tailWord_400004).sum := by decide
  have hdescent : baseEnd_400004 < baseStart_400004 := by decide
  rcases family_descends (prefixWord ++ tailWord_400004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400018 : List Nat := [3, 2, 3, 1, 2, 1, 4, 1, 3]
def baseStart_400018 : Nat := 118140960795 + 400018 * 2 ^ 59
def prefixEnd_400018 : Nat := 4983230072969 + 3 ^ 40 * 400018 * 2
def baseEnd_400018 : Nat := 182579115066952143498095

theorem tailTrace_400018 : CollatzResearch.WordTrace tailWord_400018 prefixEnd_400018 182579115066952143498095 := by
  unfold tailWord_400018
  simp only [CollatzResearch.WordTrace]
  refine ⟨3647463766202644620116177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9726570043207052320309805 3647463766202644620116177)
  ·
    refine ⟨2735597824651983465087133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3647463766202644620116177 2735597824651983465087133)
    ·
      refine ⟨1025849184244493799407675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2735597824651983465087133 1025849184244493799407675)
      ·
        refine ⟨1538773776366740699111513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025849184244493799407675 1538773776366740699111513)
        ·
          refine ⟨1154080332275055524333635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1538773776366740699111513 1154080332275055524333635)
          ·
            refine ⟨1731120498412583286500453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154080332275055524333635 1731120498412583286500453)
            ·
              refine ⟨324585093452359366218835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1731120498412583286500453 324585093452359366218835)
              ·
                refine ⟨486877640178539049328253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324585093452359366218835 486877640178539049328253)
                ·
                  refine ⟨182579115066952143498095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 486877640178539049328253 182579115066952143498095)
                  ·
                    rfl

theorem cell20_400018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_400018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400018 prefixEnd_400018 := by exact prefixLift 400018
  have htrace : WordTrace (prefixWord ++ tailWord_400018) baseStart_400018 baseEnd_400018 := by
    simpa [prefixWord, tailWord_400018, baseEnd_400018] using wordTrace_append hprefix tailTrace_400018
  have hstable : (prefixWord ++ tailWord_400018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400018).length < 2 ^ (prefixWord ++ tailWord_400018).sum := by decide
  have hdescent : baseEnd_400018 < baseStart_400018 := by decide
  rcases family_descends (prefixWord ++ tailWord_400018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400029 : List Nat := [1, 4, 2, 1, 1, 1, 2, 4, 4]
def baseStart_400029 : Nat := 118140960795 + 400029 * 2 ^ 59
def prefixEnd_400029 : Nat := 4983230072969 + 3 ^ 40 * 400029 * 2
def baseEnd_400029 : Nat := 182584135766684994131383

theorem tailTrace_400029 : CollatzResearch.WordTrace tailWord_400029 prefixEnd_400029 182584135766684994131383 := by
  unfold tailWord_400029
  simp only [CollatzResearch.WordTrace]
  refine ⟨14590256267770727359115141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9726837511847151572743427 14590256267770727359115141)
  ·
    refine ⟨2735673050207011379834089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14590256267770727359115141 2735673050207011379834089)
    ·
      refine ⟨2051754787655258534875567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2735673050207011379834089 2051754787655258534875567)
      ·
        refine ⟨3077632181482887802313351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2051754787655258534875567 3077632181482887802313351)
        ·
          refine ⟨4616448272224331703470027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3077632181482887802313351 4616448272224331703470027)
          ·
            refine ⟨6924672408336497555205041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4616448272224331703470027 6924672408336497555205041)
            ·
              refine ⟨5193504306252373166403781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6924672408336497555205041 5193504306252373166403781)
              ·
                refine ⟨973782057422319968700709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5193504306252373166403781 973782057422319968700709)
                ·
                  refine ⟨182584135766684994131383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 973782057422319968700709 182584135766684994131383)
                  ·
                    rfl

theorem cell20_400029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_400029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400029 prefixEnd_400029 := by exact prefixLift 400029
  have htrace : WordTrace (prefixWord ++ tailWord_400029) baseStart_400029 baseEnd_400029 := by
    simpa [prefixWord, tailWord_400029, baseEnd_400029] using wordTrace_append hprefix tailTrace_400029
  have hstable : (prefixWord ++ tailWord_400029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400029).length < 2 ^ (prefixWord ++ tailWord_400029).sum := by decide
  have hdescent : baseEnd_400029 < baseStart_400029 := by decide
  rcases family_descends (prefixWord ++ tailWord_400029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400036 : List Nat := [2, 3, 1, 2, 2, 1, 1, 8]
def baseStart_400036 : Nat := 118140960795 + 400036 * 2 ^ 59
def prefixEnd_400036 : Nat := 4983230072969 + 3 ^ 40 * 400036 * 2
def baseEnd_400036 : Nat := 60862443585808026966007

theorem tailTrace_400036 : CollatzResearch.WordTrace tailWord_400036 prefixEnd_400036 60862443585808026966007 := by
  unfold tailWord_400036
  simp only [CollatzResearch.WordTrace]
  refine ⟨7295255789372683777309981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9727007719163578369746641 7295255789372683777309981)
  ·
    refine ⟨2735720921014756416491243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7295255789372683777309981 2735720921014756416491243)
    ·
      refine ⟨4103581381522134624736865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2735720921014756416491243 4103581381522134624736865)
      ·
        refine ⟨3077686036141600968552649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4103581381522134624736865 3077686036141600968552649)
        ·
          refine ⟨2308264527106200726414487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3077686036141600968552649 2308264527106200726414487)
          ·
            refine ⟨3462396790659301089621731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308264527106200726414487 3462396790659301089621731)
            ·
              refine ⟨5193595185988951634432597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462396790659301089621731 5193595185988951634432597)
              ·
                refine ⟨60862443585808026966007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5193595185988951634432597 60862443585808026966007)
                ·
                  rfl

theorem cell20_400036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_400036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400036 prefixEnd_400036 := by exact prefixLift 400036
  have htrace : WordTrace (prefixWord ++ tailWord_400036) baseStart_400036 baseEnd_400036 := by
    simpa [prefixWord, tailWord_400036, baseEnd_400036] using wordTrace_append hprefix tailTrace_400036
  have hstable : (prefixWord ++ tailWord_400036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400036).length < 2 ^ (prefixWord ++ tailWord_400036).sum := by decide
  have hdescent : baseEnd_400036 < baseStart_400036 := by decide
  rcases family_descends (prefixWord ++ tailWord_400036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400063 : List Nat := [1, 1, 2, 2, 2, 4, 4, 2, 2]
def baseStart_400063 : Nat := 118140960795 + 400063 * 2 ^ 59
def prefixEnd_400063 : Nat := 4983230072969 + 3 ^ 40 * 400063 * 2
def baseEnd_400063 : Nat := 182599654293131986997911

theorem tailTrace_400063 : CollatzResearch.WordTrace tailWord_400063 prefixEnd_400063 182599654293131986997911 := by
  unfold tailWord_400063
  simp only [CollatzResearch.WordTrace]
  refine ⟨14591496349647551165852843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9727664233098367443901895 14591496349647551165852843)
  ·
    refine ⟨21887244524471326748779265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14591496349647551165852843 21887244524471326748779265)
    ·
      refine ⟨16415433393353495061584449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21887244524471326748779265 16415433393353495061584449)
      ·
        refine ⟨12311575045015121296188337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16415433393353495061584449 12311575045015121296188337)
        ·
          refine ⟨9233681283761340972141253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12311575045015121296188337 9233681283761340972141253)
          ·
            refine ⟨1731315240705251432276485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9233681283761340972141253 1731315240705251432276485)
            ·
              refine ⟨324621607632234643551841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1731315240705251432276485 324621607632234643551841)
              ·
                refine ⟨243466205724175982663881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324621607632234643551841 243466205724175982663881)
                ·
                  refine ⟨182599654293131986997911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243466205724175982663881 182599654293131986997911)
                  ·
                    rfl

theorem cell20_400063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 2].length) (baseStart_400063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400063 prefixEnd_400063 := by exact prefixLift 400063
  have htrace : WordTrace (prefixWord ++ tailWord_400063) baseStart_400063 baseEnd_400063 := by
    simpa [prefixWord, tailWord_400063, baseEnd_400063] using wordTrace_append hprefix tailTrace_400063
  have hstable : (prefixWord ++ tailWord_400063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400063).length < 2 ^ (prefixWord ++ tailWord_400063).sum := by decide
  have hdescent : baseEnd_400063 < baseStart_400063 := by decide
  rcases family_descends (prefixWord ++ tailWord_400063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400101 : List Nat := [1, 3, 1, 4, 1, 3, 2, 3, 2]
def baseStart_400101 : Nat := 118140960795 + 400101 * 2 ^ 59
def prefixEnd_400101 : Nat := 4983230072969 + 3 ^ 40 * 400101 * 2
def baseEnd_400101 : Nat := 182616998528572743731089

theorem tailTrace_400101 : CollatzResearch.WordTrace tailWord_400101 prefixEnd_400101 182616998528572743731089 := by
  unfold tailWord_400101
  simp only [CollatzResearch.WordTrace]
  refine ⟨14592882323509883655736157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9728588215673255770490771 14592882323509883655736157)
  ·
    refine ⟨5472330871316206370901059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14592882323509883655736157 5472330871316206370901059)
    ·
      refine ⟨8208496306974309556351589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5472330871316206370901059 8208496306974309556351589)
      ·
        refine ⟨1539093057557683041815923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8208496306974309556351589 1539093057557683041815923)
        ·
          refine ⟨2308639586336524562723885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1539093057557683041815923 2308639586336524562723885)
          ·
            refine ⟨865739844876196711021457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2308639586336524562723885 865739844876196711021457)
            ·
              refine ⟨649304883657147533266093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865739844876196711021457 649304883657147533266093)
              ·
                refine ⟨243489331371430324974785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 649304883657147533266093 243489331371430324974785)
                ·
                  refine ⟨182616998528572743731089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243489331371430324974785 182616998528572743731089)
                  ·
                    rfl

theorem cell20_400101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_400101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400101 prefixEnd_400101 := by exact prefixLift 400101
  have htrace : WordTrace (prefixWord ++ tailWord_400101) baseStart_400101 baseEnd_400101 := by
    simpa [prefixWord, tailWord_400101, baseEnd_400101] using wordTrace_append hprefix tailTrace_400101
  have hstable : (prefixWord ++ tailWord_400101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400101).length < 2 ^ (prefixWord ++ tailWord_400101).sum := by decide
  have hdescent : baseEnd_400101 < baseStart_400101 := by decide
  rcases family_descends (prefixWord ++ tailWord_400101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400122 : List Nat := [3, 1, 1, 1, 1, 3, 4, 4, 2]
def baseStart_400122 : Nat := 118140960795 + 400122 * 2 ^ 59
def prefixEnd_400122 : Nat := 4983230072969 + 3 ^ 40 * 400122 * 2
def baseEnd_400122 : Nat := 182626583500790004031003

theorem tailTrace_400122 : CollatzResearch.WordTrace tailWord_400122 prefixEnd_400122 182626583500790004031003 := by
  unfold tailWord_400122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648412064108451060562655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9729098837622536161500413 3648412064108451060562655)
  ·
    refine ⟨5472618096162676590843983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3648412064108451060562655 5472618096162676590843983)
    ·
      refine ⟨8208927144244014886265975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5472618096162676590843983 8208927144244014886265975)
      ·
        refine ⟨12313390716366022329398963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8208927144244014886265975 12313390716366022329398963)
        ·
          refine ⟨18470086074549033494098445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12313390716366022329398963 18470086074549033494098445)
          ·
            refine ⟨6926282277955887560286917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18470086074549033494098445 6926282277955887560286917)
            ·
              refine ⟨1298677927116728917553797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6926282277955887560286917 1298677927116728917553797)
              ·
                refine ⟨243502111334386672041337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1298677927116728917553797 243502111334386672041337)
                ·
                  refine ⟨182626583500790004031003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243502111334386672041337 182626583500790004031003)
                  ·
                    rfl

theorem cell20_400122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_400122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400122 prefixEnd_400122 := by exact prefixLift 400122
  have htrace : WordTrace (prefixWord ++ tailWord_400122) baseStart_400122 baseEnd_400122 := by
    simpa [prefixWord, tailWord_400122, baseEnd_400122] using wordTrace_append hprefix tailTrace_400122
  have hstable : (prefixWord ++ tailWord_400122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400122).length < 2 ^ (prefixWord ++ tailWord_400122).sum := by decide
  have hdescent : baseEnd_400122 < baseStart_400122 := by decide
  rcases family_descends (prefixWord ++ tailWord_400122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400146 : List Nat := [3, 2, 4, 1, 2, 1, 1, 6]
def baseStart_400146 : Nat := 118140960795 + 400146 * 2 ^ 59
def prefixEnd_400146 : Nat := 4983230072969 + 3 ^ 40 * 400146 * 2
def baseEnd_400146 : Nat := 60879179251584195743635

theorem tailTrace_400146 : CollatzResearch.WordTrace tailWord_400146 prefixEnd_400146 60879179251584195743635 := by
  unfold tailWord_400146
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648630902086714085281073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9729682405564570894082861 3648630902086714085281073)
  ·
    refine ⟨2736473176565035563960805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3648630902086714085281073 2736473176565035563960805)
    ·
      refine ⟨513088720605944168242651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2736473176565035563960805 513088720605944168242651)
      ·
        refine ⟨769633080908916252363977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513088720605944168242651 769633080908916252363977)
        ·
          refine ⟨577224810681687189272983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 769633080908916252363977 577224810681687189272983)
          ·
            refine ⟨865837216022530783909475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577224810681687189272983 865837216022530783909475)
            ·
              refine ⟨1298755824033796175864213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865837216022530783909475 1298755824033796175864213)
              ·
                refine ⟨60879179251584195743635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1298755824033796175864213 60879179251584195743635)
                ·
                  rfl

theorem cell20_400146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_400146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400146 prefixEnd_400146 := by exact prefixLift 400146
  have htrace : WordTrace (prefixWord ++ tailWord_400146) baseStart_400146 baseEnd_400146 := by
    simpa [prefixWord, tailWord_400146, baseEnd_400146] using wordTrace_append hprefix tailTrace_400146
  have hstable : (prefixWord ++ tailWord_400146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400146).length < 2 ^ (prefixWord ++ tailWord_400146).sum := by decide
  have hdescent : baseEnd_400146 < baseStart_400146 := by decide
  rcases family_descends (prefixWord ++ tailWord_400146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400173 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 4]
def baseStart_400173 : Nat := 118140960795 + 400173 * 2 ^ 59
def prefixEnd_400173 : Nat := 4983230072969 + 3 ^ 40 * 400173 * 2
def baseEnd_400173 : Nat := 182649861290460493330795

theorem tailTrace_400173 : CollatzResearch.WordTrace tailWord_400173 prefixEnd_400173 182649861290460493330795 := by
  unfold tailWord_400173
  simp only [CollatzResearch.WordTrace]
  refine ⟨14595508379249039952357173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9730338919499359968238115 14595508379249039952357173)
  ·
    refine ⟨1368328910554597495533485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14595508379249039952357173 1368328910554597495533485)
    ·
      refine ⟨513123341457974060825057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1368328910554597495533485 513123341457974060825057)
      ·
        refine ⟨384842506093480545618793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 513123341457974060825057 384842506093480545618793)
        ·
          refine ⟨288631879570110409214095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 384842506093480545618793 288631879570110409214095)
          ·
            refine ⟨432947819355165613821143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288631879570110409214095 432947819355165613821143)
            ·
              refine ⟨649421729032748420731715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 432947819355165613821143 649421729032748420731715)
              ·
                refine ⟨974132593549122631097573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649421729032748420731715 974132593549122631097573)
                ·
                  refine ⟨182649861290460493330795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 974132593549122631097573 182649861290460493330795)
                  ·
                    rfl

theorem cell20_400173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_400173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400173 prefixEnd_400173 := by exact prefixLift 400173
  have htrace : WordTrace (prefixWord ++ tailWord_400173) baseStart_400173 baseEnd_400173 := by
    simpa [prefixWord, tailWord_400173, baseEnd_400173] using wordTrace_append hprefix tailTrace_400173
  have hstable : (prefixWord ++ tailWord_400173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400173).length < 2 ^ (prefixWord ++ tailWord_400173).sum := by decide
  have hdescent : baseEnd_400173 < baseStart_400173 := by decide
  rcases family_descends (prefixWord ++ tailWord_400173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400177 : List Nat := [1, 2, 2, 3, 2, 1, 5, 2, 2]
def baseStart_400177 : Nat := 118140960795 + 400177 * 2 ^ 59
def prefixEnd_400177 : Nat := 4983230072969 + 3 ^ 40 * 400177 * 2
def baseEnd_400177 : Nat := 182651686999454257197445

theorem tailTrace_400177 : CollatzResearch.WordTrace tailWord_400177 prefixEnd_400177 182651686999454257197445 := by
  unfold tailWord_400177
  simp only [CollatzResearch.WordTrace]
  refine ⟨14595654271234548635502785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9730436180823032423668523 14595654271234548635502785)
  ·
    refine ⟨10946740703425911476627089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14595654271234548635502785 10946740703425911476627089)
    ·
      refine ⟨8210055527569433607470317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10946740703425911476627089 8210055527569433607470317)
      ·
        refine ⟨3078770822838537602801369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8210055527569433607470317 3078770822838537602801369)
        ·
          refine ⟨2309078117128903202101027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3078770822838537602801369 2309078117128903202101027)
          ·
            refine ⟨3463617175693354803151541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2309078117128903202101027 3463617175693354803151541)
            ·
              refine ⟨324714110221252012795457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3463617175693354803151541 324714110221252012795457)
              ·
                refine ⟨243535582665939009596593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324714110221252012795457 243535582665939009596593)
                ·
                  refine ⟨182651686999454257197445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243535582665939009596593 182651686999454257197445)
                  ·
                    rfl

theorem cell20_400177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 2].length) (baseStart_400177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400177 prefixEnd_400177 := by exact prefixLift 400177
  have htrace : WordTrace (prefixWord ++ tailWord_400177) baseStart_400177 baseEnd_400177 := by
    simpa [prefixWord, tailWord_400177, baseEnd_400177] using wordTrace_append hprefix tailTrace_400177
  have hstable : (prefixWord ++ tailWord_400177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400177).length < 2 ^ (prefixWord ++ tailWord_400177).sum := by decide
  have hdescent : baseEnd_400177 < baseStart_400177 := by decide
  rcases family_descends (prefixWord ++ tailWord_400177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400191 : List Nat := [1, 1, 2, 2, 5, 1, 4, 1, 3]
def baseStart_400191 : Nat := 118140960795 + 400191 * 2 ^ 59
def prefixEnd_400191 : Nat := 4983230072969 + 3 ^ 40 * 400191 * 2
def baseEnd_400191 : Nat := 182658076980932430730721

theorem tailTrace_400191 : CollatzResearch.WordTrace tailWord_400191 prefixEnd_400191 182658076980932430730721 := by
  unfold tailWord_400191
  simp only [CollatzResearch.WordTrace]
  refine ⟨14596164893183829026512427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9730776595455886017674951 14596164893183829026512427)
  ·
    refine ⟨21894247339775743539768641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14596164893183829026512427 21894247339775743539768641)
    ·
      refine ⟨16420685504831807654826481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21894247339775743539768641 16420685504831807654826481)
      ·
        refine ⟨12315514128623855741119861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16420685504831807654826481 12315514128623855741119861)
        ·
          refine ⟨1154579449558486475729987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12315514128623855741119861 1154579449558486475729987)
          ·
            refine ⟨1731869174337729713594981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154579449558486475729987 1731869174337729713594981)
            ·
              refine ⟨324725470188324321299059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1731869174337729713594981 324725470188324321299059)
              ·
                refine ⟨487088205282486481948589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324725470188324321299059 487088205282486481948589)
                ·
                  refine ⟨182658076980932430730721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487088205282486481948589 182658076980932430730721)
                  ·
                    rfl

theorem cell20_400191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 3].length) (baseStart_400191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400191 prefixEnd_400191 := by exact prefixLift 400191
  have htrace : WordTrace (prefixWord ++ tailWord_400191) baseStart_400191 baseEnd_400191 := by
    simpa [prefixWord, tailWord_400191, baseEnd_400191] using wordTrace_append hprefix tailTrace_400191
  have hstable : (prefixWord ++ tailWord_400191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400191).length < 2 ^ (prefixWord ++ tailWord_400191).sum := by decide
  have hdescent : baseEnd_400191 < baseStart_400191 := by decide
  rcases family_descends (prefixWord ++ tailWord_400191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400226 : List Nat := [3, 3, 2, 1, 11]
def baseStart_400226 : Nat := 118140960795 + 400226 * 2 ^ 59
def prefixEnd_400226 : Nat := 4983230072969 + 3 ^ 40 * 400226 * 2
def baseEnd_400226 : Nat := 2255235209069479809431

theorem tailTrace_400226 : CollatzResearch.WordTrace tailWord_400226 prefixEnd_400226 2255235209069479809431 := by
  unfold tailWord_400226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3649360362014257501009133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9731627632038020002691021 3649360362014257501009133)
  ·
    refine ⟨1368510135755346562878425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3649360362014257501009133 1368510135755346562878425)
    ·
      refine ⟨1026382601816509922158819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1368510135755346562878425 1026382601816509922158819)
      ·
        refine ⟨1539573902724764883238229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1026382601816509922158819 1539573902724764883238229)
        ·
          refine ⟨2255235209069479809431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1539573902724764883238229 2255235209069479809431)
          ·
            rfl

theorem cell20_400226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 11].length) (baseStart_400226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400226 prefixEnd_400226 := by exact prefixLift 400226
  have htrace : WordTrace (prefixWord ++ tailWord_400226) baseStart_400226 baseEnd_400226 := by
    simpa [prefixWord, tailWord_400226, baseEnd_400226] using wordTrace_append hprefix tailTrace_400226
  have hstable : (prefixWord ++ tailWord_400226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400226).length < 2 ^ (prefixWord ++ tailWord_400226).sum := by decide
  have hdescent : baseEnd_400226 < baseStart_400226 := by decide
  rcases family_descends (prefixWord ++ tailWord_400226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400232 : List Nat := [2, 1, 4, 2, 1, 4, 2, 2, 2]
def baseStart_400232 : Nat := 118140960795 + 400232 * 2 ^ 59
def prefixEnd_400232 : Nat := 4983230072969 + 3 ^ 40 * 400232 * 2
def baseEnd_400232 : Nat := 182676790498118510363887

theorem tailTrace_400232 : CollatzResearch.WordTrace tailWord_400232 prefixEnd_400232 182676790498118510363887 := by
  unfold tailWord_400232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7298830143017646514377475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9731773524023528685836633 7298830143017646514377475)
  ·
    refine ⟨10948245214526469771566213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7298830143017646514377475 10948245214526469771566213)
    ·
      refine ⟨2052795977723713082168665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10948245214526469771566213 2052795977723713082168665)
      ·
        refine ⟨1539596983292784811626499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2052795977723713082168665 1539596983292784811626499)
        ·
          refine ⟨2309395474939177217439749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1539596983292784811626499 2309395474939177217439749)
          ·
            refine ⟨433011651551095728269953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2309395474939177217439749 433011651551095728269953)
            ·
              refine ⟨324758738663321796202465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433011651551095728269953 324758738663321796202465)
              ·
                refine ⟨243569053997491347151849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324758738663321796202465 243569053997491347151849)
                ·
                  refine ⟨182676790498118510363887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243569053997491347151849 182676790498118510363887)
                  ·
                    rfl

theorem cell20_400232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 2].length) (baseStart_400232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400232 prefixEnd_400232 := by exact prefixLift 400232
  have htrace : WordTrace (prefixWord ++ tailWord_400232) baseStart_400232 baseEnd_400232 := by
    simpa [prefixWord, tailWord_400232, baseEnd_400232] using wordTrace_append hprefix tailTrace_400232
  have hstable : (prefixWord ++ tailWord_400232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400232).length < 2 ^ (prefixWord ++ tailWord_400232).sum := by decide
  have hdescent : baseEnd_400232 < baseStart_400232 := by decide
  rcases family_descends (prefixWord ++ tailWord_400232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400236 : List Nat := [2, 2, 1, 1, 4, 1, 3, 4, 2]
def baseStart_400236 : Nat := 118140960795 + 400236 * 2 ^ 59
def prefixEnd_400236 : Nat := 4983230072969 + 3 ^ 40 * 400236 * 2
def baseEnd_400236 : Nat := 182678616207112274230537

theorem tailTrace_400236 : CollatzResearch.WordTrace tailWord_400236 prefixEnd_400236 182678616207112274230537 := by
  unfold tailWord_400236
  simp only [CollatzResearch.WordTrace]
  refine ⟨7298903089010400855950281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9731870785347201141267041 7298903089010400855950281)
  ·
    refine ⟨5474177316757800641962711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7298903089010400855950281 5474177316757800641962711)
    ·
      refine ⟨8211265975136700962944067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5474177316757800641962711 8211265975136700962944067)
      ·
        refine ⟨12316898962705051444416101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8211265975136700962944067 12316898962705051444416101)
        ·
          refine ⟨2309418555507197145828019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12316898962705051444416101 2309418555507197145828019)
          ·
            refine ⟨3464127833260795718742029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2309418555507197145828019 3464127833260795718742029)
            ·
              refine ⟨1299047937472798394528261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3464127833260795718742029 1299047937472798394528261)
              ·
                refine ⟨243571488276149698974049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1299047937472798394528261 243571488276149698974049)
                ·
                  refine ⟨182678616207112274230537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243571488276149698974049 182678616207112274230537)
                  ·
                    rfl

theorem cell20_400236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_400236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400236 prefixEnd_400236 := by exact prefixLift 400236
  have htrace : WordTrace (prefixWord ++ tailWord_400236) baseStart_400236 baseEnd_400236 := by
    simpa [prefixWord, tailWord_400236, baseEnd_400236] using wordTrace_append hprefix tailTrace_400236
  have hstable : (prefixWord ++ tailWord_400236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400236).length < 2 ^ (prefixWord ++ tailWord_400236).sum := by decide
  have hdescent : baseEnd_400236 < baseStart_400236 := by decide
  rcases family_descends (prefixWord ++ tailWord_400236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400284 : List Nat := [2, 2, 3, 3, 2, 2, 1, 2, 3]
def baseStart_400284 : Nat := 118140960795 + 400284 * 2 ^ 59
def prefixEnd_400284 : Nat := 4983230072969 + 3 ^ 40 * 400284 * 2
def baseEnd_400284 : Nat := 182700524715037440630341

theorem tailTrace_400284 : CollatzResearch.WordTrace tailWord_400284 prefixEnd_400284 182700524715037440630341 := by
  unfold tailWord_400284
  simp only [CollatzResearch.WordTrace]
  refine ⟨7299778440923452954823953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9733037921231270606431937 7299778440923452954823953)
  ·
    refine ⟨5474833830692589716117965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7299778440923452954823953 5474833830692589716117965)
    ·
      refine ⟨2053062686509721143544237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5474833830692589716117965 2053062686509721143544237)
      ·
        refine ⟨769898507441145428829089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2053062686509721143544237 769898507441145428829089)
        ·
          refine ⟨577423880580859071621817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 769898507441145428829089 577423880580859071621817)
          ·
            refine ⟨433067910435644303716363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 577423880580859071621817 433067910435644303716363)
            ·
              refine ⟨649601865653466455574545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433067910435644303716363 649601865653466455574545)
              ·
                refine ⟨487201399240099841680909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649601865653466455574545 487201399240099841680909)
                ·
                  refine ⟨182700524715037440630341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487201399240099841680909 182700524715037440630341)
                  ·
                    rfl

theorem cell20_400284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_400284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400284 prefixEnd_400284 := by exact prefixLift 400284
  have htrace : WordTrace (prefixWord ++ tailWord_400284) baseStart_400284 baseEnd_400284 := by
    simpa [prefixWord, tailWord_400284, baseEnd_400284] using wordTrace_append hprefix tailTrace_400284
  have hstable : (prefixWord ++ tailWord_400284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400284).length < 2 ^ (prefixWord ++ tailWord_400284).sum := by decide
  have hdescent : baseEnd_400284 < baseStart_400284 := by decide
  rcases family_descends (prefixWord ++ tailWord_400284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400288 : List Nat := [2, 1, 1, 4, 1, 1, 5, 2, 3]
def baseStart_400288 : Nat := 118140960795 + 400288 * 2 ^ 59
def prefixEnd_400288 : Nat := 4983230072969 + 3 ^ 40 * 400288 * 2
def baseEnd_400288 : Nat := 182702350424031204496991

theorem tailTrace_400288 : CollatzResearch.WordTrace tailWord_400288 prefixEnd_400288 182702350424031204496991 := by
  unfold tailWord_400288
  simp only [CollatzResearch.WordTrace]
  refine ⟨7299851386916207296396759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9733135182554943061862345 7299851386916207296396759)
  ·
    refine ⟨10949777080374310944595139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7299851386916207296396759 10949777080374310944595139)
    ·
      refine ⟨16424665620561466416892709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10949777080374310944595139 16424665620561466416892709)
      ·
        refine ⟨3079624803855274953167383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16424665620561466416892709 3079624803855274953167383)
        ·
          refine ⟨4619437205782912429751075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3079624803855274953167383 4619437205782912429751075)
          ·
            refine ⟨6929155808674368644626613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4619437205782912429751075 6929155808674368644626613)
            ·
              refine ⟨649608357063222060433745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6929155808674368644626613 649608357063222060433745)
              ·
                refine ⟨487206267797416545325309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649608357063222060433745 487206267797416545325309)
                ·
                  refine ⟨182702350424031204496991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487206267797416545325309 182702350424031204496991)
                  ·
                    rfl

theorem cell20_400288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_400288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400288 prefixEnd_400288 := by exact prefixLift 400288
  have htrace : WordTrace (prefixWord ++ tailWord_400288) baseStart_400288 baseEnd_400288 := by
    simpa [prefixWord, tailWord_400288, baseEnd_400288] using wordTrace_append hprefix tailTrace_400288
  have hstable : (prefixWord ++ tailWord_400288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400288).length < 2 ^ (prefixWord ++ tailWord_400288).sum := by decide
  have hdescent : baseEnd_400288 < baseStart_400288 := by decide
  rcases family_descends (prefixWord ++ tailWord_400288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400301 : List Nat := [1, 5, 2, 3, 1, 1, 3, 1, 3]
def baseStart_400301 : Nat := 118140960795 + 400301 * 2 ^ 59
def prefixEnd_400301 : Nat := 4983230072969 + 3 ^ 40 * 400301 * 2
def baseEnd_400301 : Nat := 182708283978260937063605

theorem tailTrace_400301 : CollatzResearch.WordTrace tailWord_400301 prefixEnd_400301 182708283978260937063605 := by
  unfold tailWord_400301
  simp only [CollatzResearch.WordTrace]
  refine ⟨14600176922785317813016757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9733451281856878542011171 14600176922785317813016757)
  ·
    refine ⟨1368766586511123544970321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14600176922785317813016757 1368766586511123544970321)
    ·
      refine ⟨1026574939883342658727741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1368766586511123544970321 1026574939883342658727741)
      ·
        refine ⟨384965602456253497022903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1026574939883342658727741 384965602456253497022903)
        ·
          refine ⟨577448403684380245534355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 384965602456253497022903 577448403684380245534355)
          ·
            refine ⟨866172605526570368301533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577448403684380245534355 866172605526570368301533)
            ·
              refine ⟨324814727072463888113075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 866172605526570368301533 324814727072463888113075)
              ·
                refine ⟨487222090608695832169613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324814727072463888113075 487222090608695832169613)
                ·
                  refine ⟨182708283978260937063605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487222090608695832169613 182708283978260937063605)
                  ·
                    rfl

theorem cell20_400301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_400301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400301 prefixEnd_400301 := by exact prefixLift 400301
  have htrace : WordTrace (prefixWord ++ tailWord_400301) baseStart_400301 baseEnd_400301 := by
    simpa [prefixWord, tailWord_400301, baseEnd_400301] using wordTrace_append hprefix tailTrace_400301
  have hstable : (prefixWord ++ tailWord_400301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400301).length < 2 ^ (prefixWord ++ tailWord_400301).sum := by decide
  have hdescent : baseEnd_400301 < baseStart_400301 := by decide
  rcases family_descends (prefixWord ++ tailWord_400301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400323 : List Nat := [1, 1, 1, 3, 1, 1, 2, 10]
def baseStart_400323 : Nat := 118140960795 + 400323 * 2 ^ 59
def prefixEnd_400323 : Nat := 4983230072969 + 3 ^ 40 * 400323 * 2
def baseEnd_400323 : Nat := 60906108459242212776727

theorem tailTrace_400323 : CollatzResearch.WordTrace tailWord_400323 prefixEnd_400323 60906108459242212776727 := by
  unfold tailWord_400323
  simp only [CollatzResearch.WordTrace]
  refine ⟨14600979328705615570317623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9733986219137077046878415 14600979328705615570317623)
  ·
    refine ⟨21901468993058423355476435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14600979328705615570317623 21901468993058423355476435)
    ·
      refine ⟨32852203489587635033214653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21901468993058423355476435 32852203489587635033214653)
      ·
        refine ⟨12319576308595363137455495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32852203489587635033214653 12319576308595363137455495)
        ·
          refine ⟨18479364462893044706183243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12319576308595363137455495 18479364462893044706183243)
          ·
            refine ⟨27719046694339567059274865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18479364462893044706183243 27719046694339567059274865)
            ·
              refine ⟨20789285020754675294456149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27719046694339567059274865 20789285020754675294456149)
              ·
                refine ⟨60906108459242212776727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20789285020754675294456149 60906108459242212776727)
                ·
                  rfl

theorem cell20_400323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 10].length) (baseStart_400323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400323 prefixEnd_400323 := by exact prefixLift 400323
  have htrace : WordTrace (prefixWord ++ tailWord_400323) baseStart_400323 baseEnd_400323 := by
    simpa [prefixWord, tailWord_400323, baseEnd_400323] using wordTrace_append hprefix tailTrace_400323
  have hstable : (prefixWord ++ tailWord_400323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400323).length < 2 ^ (prefixWord ++ tailWord_400323).sum := by decide
  have hdescent : baseEnd_400323 < baseStart_400323 := by decide
  rcases family_descends (prefixWord ++ tailWord_400323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400340 : List Nat := [2, 4, 1, 2, 1, 2, 8]
def baseStart_400340 : Nat := 118140960795 + 400340 * 2 ^ 59
def prefixEnd_400340 : Nat := 4983230072969 + 3 ^ 40 * 400340 * 2
def baseEnd_400340 : Nat := 20302898293438903862605

theorem tailTrace_400340 : CollatzResearch.WordTrace tailWord_400340 prefixEnd_400340 20302898293438903862605 := by
  unfold tailWord_400340
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300799684822013736843237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9734399579762684982457649 7300799684822013736843237)
  ·
    refine ⟨1368899940904127575658107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7300799684822013736843237 1368899940904127575658107)
    ·
      refine ⟨2053349911356191363487161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1368899940904127575658107 2053349911356191363487161)
      ·
        refine ⟨1540012433517143522615371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2053349911356191363487161 1540012433517143522615371)
        ·
          refine ⟨2310018650275715283923057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1540012433517143522615371 2310018650275715283923057)
          ·
            refine ⟨1732513987706786462942293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2310018650275715283923057 1732513987706786462942293)
            ·
              refine ⟨20302898293438903862605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1732513987706786462942293 20302898293438903862605)
              ·
                rfl

theorem cell20_400340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 8].length) (baseStart_400340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400340 prefixEnd_400340 := by exact prefixLift 400340
  have htrace : WordTrace (prefixWord ++ tailWord_400340) baseStart_400340 baseEnd_400340 := by
    simpa [prefixWord, tailWord_400340, baseEnd_400340] using wordTrace_append hprefix tailTrace_400340
  have hstable : (prefixWord ++ tailWord_400340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400340).length < 2 ^ (prefixWord ++ tailWord_400340).sum := by decide
  have hdescent : baseEnd_400340 < baseStart_400340 := by decide
  rcases family_descends (prefixWord ++ tailWord_400340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400405 : List Nat := [1, 3, 2, 1, 4, 1, 4, 2, 2]
def baseStart_400405 : Nat := 118140960795 + 400405 * 2 ^ 59
def prefixEnd_400405 : Nat := 4983230072969 + 3 ^ 40 * 400405 * 2
def baseEnd_400405 : Nat := 182755752412098797596513

theorem tailTrace_400405 : CollatzResearch.WordTrace tailWord_400405 prefixEnd_400405 182755752412098797596513 := by
  unfold tailWord_400405
  simp only [CollatzResearch.WordTrace]
  refine ⟨14603970114408543574802669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9735980076272362383201779 14603970114408543574802669)
  ·
    refine ⟨5476488792903203840551001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14603970114408543574802669 5476488792903203840551001)
    ·
      refine ⟨4107366594677402880413251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5476488792903203840551001 4107366594677402880413251)
      ·
        refine ⟨6161049892016104320619877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4107366594677402880413251 6161049892016104320619877)
        ·
          refine ⟨1155196854753019560116227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6161049892016104320619877 1155196854753019560116227)
          ·
            refine ⟨1732795282129529340174341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155196854753019560116227 1732795282129529340174341)
            ·
              refine ⟨324899115399286751282689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1732795282129529340174341 324899115399286751282689)
              ·
                refine ⟨243674336549465063462017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 324899115399286751282689 243674336549465063462017)
                ·
                  refine ⟨182755752412098797596513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243674336549465063462017 182755752412098797596513)
                  ·
                    rfl

theorem cell20_400405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_400405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400405 prefixEnd_400405 := by exact prefixLift 400405
  have htrace : WordTrace (prefixWord ++ tailWord_400405) baseStart_400405 baseEnd_400405 := by
    simpa [prefixWord, tailWord_400405, baseEnd_400405] using wordTrace_append hprefix tailTrace_400405
  have hstable : (prefixWord ++ tailWord_400405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400405).length < 2 ^ (prefixWord ++ tailWord_400405).sum := by decide
  have hdescent : baseEnd_400405 < baseStart_400405 := by decide
  rcases family_descends (prefixWord ++ tailWord_400405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400412 : List Nat := [2, 2, 3, 1, 5, 1, 1, 5]
def baseStart_400412 : Nat := 118140960795 + 400412 * 2 ^ 59
def prefixEnd_400412 : Nat := 4983230072969 + 3 ^ 40 * 400412 * 2
def baseEnd_400412 : Nat := 60919649134279294787717

theorem tailTrace_400412 : CollatzResearch.WordTrace tailWord_400412 prefixEnd_400412 60919649134279294787717 := by
  unfold tailWord_400412
  simp only [CollatzResearch.WordTrace]
  refine ⟨7302112712691591885153745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9736150283588789180204993 7302112712691591885153745)
  ·
    refine ⟨5476584534518693913865309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7302112712691591885153745 5476584534518693913865309)
    ·
      refine ⟨2053719200444510217699491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5476584534518693913865309 2053719200444510217699491)
      ·
        refine ⟨3080578800666765326549237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2053719200444510217699491 3080578800666765326549237)
        ·
          refine ⟨288804262562509249363991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3080578800666765326549237 288804262562509249363991)
          ·
            refine ⟨433206393843763874045987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288804262562509249363991 433206393843763874045987)
            ·
              refine ⟨649809590765645811068981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433206393843763874045987 649809590765645811068981)
              ·
                refine ⟨60919649134279294787717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 649809590765645811068981 60919649134279294787717)
                ·
                  rfl

theorem cell20_400412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_400412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400412 prefixEnd_400412 := by exact prefixLift 400412
  have htrace : WordTrace (prefixWord ++ tailWord_400412) baseStart_400412 baseEnd_400412 := by
    simpa [prefixWord, tailWord_400412, baseEnd_400412] using wordTrace_append hprefix tailTrace_400412
  have hstable : (prefixWord ++ tailWord_400412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400412).length < 2 ^ (prefixWord ++ tailWord_400412).sum := by decide
  have hdescent : baseEnd_400412 < baseStart_400412 := by decide
  rcases family_descends (prefixWord ++ tailWord_400412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400426 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 4]
def baseStart_400426 : Nat := 118140960795 + 400426 * 2 ^ 59
def prefixEnd_400426 : Nat := 4983230072969 + 3 ^ 40 * 400426 * 2
def baseEnd_400426 : Nat := 182765337384316057896427

theorem tailTrace_400426 : CollatzResearch.WordTrace tailWord_400426 prefixEnd_400426 182765337384316057896427 := by
  unfold tailWord_400426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3651184011833116040329283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9736490698221642774211421 3651184011833116040329283)
  ·
    refine ⟨5476776017749674060493925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3651184011833116040329283 5476776017749674060493925)
    ·
      refine ⟨1026895503328063886342611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5476776017749674060493925 1026895503328063886342611)
      ·
        refine ⟨1540343254992095829513917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1026895503328063886342611 1540343254992095829513917)
        ·
          refine ⟨577628720622035936067719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1540343254992095829513917 577628720622035936067719)
          ·
            refine ⟨866443080933053904101579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577628720622035936067719 866443080933053904101579)
            ·
              refine ⟨1299664621399580856152369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866443080933053904101579 1299664621399580856152369)
              ·
                refine ⟨974748466049685642114277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1299664621399580856152369 974748466049685642114277)
                ·
                  refine ⟨182765337384316057896427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 974748466049685642114277 182765337384316057896427)
                  ·
                    rfl

theorem cell20_400426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_400426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400426 prefixEnd_400426 := by exact prefixLift 400426
  have htrace : WordTrace (prefixWord ++ tailWord_400426) baseStart_400426 baseEnd_400426 := by
    simpa [prefixWord, tailWord_400426, baseEnd_400426] using wordTrace_append hprefix tailTrace_400426
  have hstable : (prefixWord ++ tailWord_400426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400426).length < 2 ^ (prefixWord ++ tailWord_400426).sum := by decide
  have hdescent : baseEnd_400426 < baseStart_400426 := by decide
  rcases family_descends (prefixWord ++ tailWord_400426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400523 : List Nat := [1, 1, 1, 1, 4, 1, 1, 8, 2]
def baseStart_400523 : Nat := 118140960795 + 400523 * 2 ^ 59
def prefixEnd_400523 : Nat := 4983230072969 + 3 ^ 40 * 400523 * 2
def baseEnd_400523 : Nat := 182809610827414831662697

theorem tailTrace_400523 : CollatzResearch.WordTrace tailWord_400523 prefixEnd_400523 182809610827414831662697 := by
  unfold tailWord_400523
  simp only [CollatzResearch.WordTrace]
  refine ⟨14608273927981049727598223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9738849285320699818398815 14608273927981049727598223)
  ·
    refine ⟨21912410891971574591397335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14608273927981049727598223 21912410891971574591397335)
    ·
      refine ⟨32868616337957361887096003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21912410891971574591397335 32868616337957361887096003)
      ·
        refine ⟨49302924506936042830644005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32868616337957361887096003 49302924506936042830644005)
        ·
          refine ⟨9244298345050508030745751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49302924506936042830644005 9244298345050508030745751)
          ·
            refine ⟨13866447517575762046118627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9244298345050508030745751 13866447517575762046118627)
            ·
              refine ⟨20799671276363643069177941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13866447517575762046118627 20799671276363643069177941)
              ·
                refine ⟨243746147769886442216929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 20799671276363643069177941 243746147769886442216929)
                ·
                  refine ⟨182809610827414831662697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243746147769886442216929 182809610827414831662697)
                  ·
                    rfl

theorem cell20_400523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 2].length) (baseStart_400523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400523 prefixEnd_400523 := by exact prefixLift 400523
  have htrace : WordTrace (prefixWord ++ tailWord_400523) baseStart_400523 baseEnd_400523 := by
    simpa [prefixWord, tailWord_400523, baseEnd_400523] using wordTrace_append hprefix tailTrace_400523
  have hstable : (prefixWord ++ tailWord_400523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400523).length < 2 ^ (prefixWord ++ tailWord_400523).sum := by decide
  have hdescent : baseEnd_400523 < baseStart_400523 := by decide
  rcases family_descends (prefixWord ++ tailWord_400523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400530 : List Nat := [3, 2, 3, 1, 1, 2, 1, 7]
def baseStart_400530 : Nat := 118140960795 + 400530 * 2 ^ 59
def prefixEnd_400530 : Nat := 4983230072969 + 3 ^ 40 * 400530 * 2
def baseEnd_400530 : Nat := 60937601939384639476445

theorem tailTrace_400530 : CollatzResearch.WordTrace tailWord_400530 prefixEnd_400530 60937601939384639476445 := by
  unfold tailWord_400530
  simp only [CollatzResearch.WordTrace]
  refine ⟨3652132309738922480775761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9739019492637126615402029 3652132309738922480775761)
  ·
    refine ⟨2739099232304191860581821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3652132309738922480775761 2739099232304191860581821)
    ·
      refine ⟨1027162212114071947718183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2739099232304191860581821 1027162212114071947718183)
      ·
        refine ⟨1540743318171107921577275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1027162212114071947718183 1540743318171107921577275)
        ·
          refine ⟨2311114977256661882365913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1540743318171107921577275 2311114977256661882365913)
          ·
            refine ⟨1733336232942496411774435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2311114977256661882365913 1733336232942496411774435)
            ·
              refine ⟨2600004349413744617661653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733336232942496411774435 2600004349413744617661653)
              ·
                refine ⟨60937601939384639476445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2600004349413744617661653 60937601939384639476445)
                ·
                  rfl

theorem cell20_400530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_400530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400530 prefixEnd_400530 := by exact prefixLift 400530
  have htrace : WordTrace (prefixWord ++ tailWord_400530) baseStart_400530 baseEnd_400530 := by
    simpa [prefixWord, tailWord_400530, baseEnd_400530] using wordTrace_append hprefix tailTrace_400530
  have hstable : (prefixWord ++ tailWord_400530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400530).length < 2 ^ (prefixWord ++ tailWord_400530).sum := by decide
  have hdescent : baseEnd_400530 < baseStart_400530 := by decide
  rcases family_descends (prefixWord ++ tailWord_400530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400544 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_400544 : Nat := 118140960795 + 400544 * 2 ^ 59
def prefixEnd_400544 : Nat := 4983230072969 + 3 ^ 40 * 400544 * 2
def baseEnd_400544 : Nat := 182819195799632091962611

theorem tailTrace_400544 : CollatzResearch.WordTrace tailWord_400544 prefixEnd_400544 182819195799632091962611 := by
  unfold tailWord_400544
  simp only [CollatzResearch.WordTrace]
  refine ⟨7304519930452485157056343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9739359907269980209408457 7304519930452485157056343)
  ·
    refine ⟨10956779895678727735584515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7304519930452485157056343 10956779895678727735584515)
    ·
      refine ⟨16435169843518091603376773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10956779895678727735584515 16435169843518091603376773)
      ·
        refine ⟨3081594345659642175633145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16435169843518091603376773 3081594345659642175633145)
        ·
          refine ⟨2311195759244731631724859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3081594345659642175633145 2311195759244731631724859)
          ·
            refine ⟨3466793638867097447587289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311195759244731631724859 3466793638867097447587289)
            ·
              refine ⟨2600095229150323085690467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3466793638867097447587289 2600095229150323085690467)
              ·
                refine ⟨3900142843725484628535701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600095229150323085690467 3900142843725484628535701)
                ·
                  refine ⟨182819195799632091962611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3900142843725484628535701 182819195799632091962611)
                  ·
                    rfl

theorem cell20_400544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_400544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400544 prefixEnd_400544 := by exact prefixLift 400544
  have htrace : WordTrace (prefixWord ++ tailWord_400544) baseStart_400544 baseEnd_400544 := by
    simpa [prefixWord, tailWord_400544, baseEnd_400544] using wordTrace_append hprefix tailTrace_400544
  have hstable : (prefixWord ++ tailWord_400544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400544).length < 2 ^ (prefixWord ++ tailWord_400544).sum := by decide
  have hdescent : baseEnd_400544 < baseStart_400544 := by decide
  rcases family_descends (prefixWord ++ tailWord_400544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400574 : List Nat := [4, 2, 1, 1, 3, 3, 2, 2, 2]
def baseStart_400574 : Nat := 118140960795 + 400574 * 2 ^ 59
def prefixEnd_400574 : Nat := 4983230072969 + 3 ^ 40 * 400574 * 2
def baseEnd_400574 : Nat := 182832888617085320962489

theorem tailTrace_400574 : CollatzResearch.WordTrace tailWord_400574 prefixEnd_400574 182832888617085320962489 := by
  unfold tailWord_400574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1826266756349535679713097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9740089367197523625136517 1826266756349535679713097)
  ·
    refine ⟨1369700067262151759784823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1826266756349535679713097 1369700067262151759784823)
    ·
      refine ⟨2054550100893227639677235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1369700067262151759784823 2054550100893227639677235)
      ·
        refine ⟨3081825151339841459515853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2054550100893227639677235 3081825151339841459515853)
        ·
          refine ⟨1155684431752440547318445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3081825151339841459515853 1155684431752440547318445)
          ·
            refine ⟨433381661907165205244417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1155684431752440547318445 433381661907165205244417)
            ·
              refine ⟨325036246430373903933313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433381661907165205244417 325036246430373903933313)
              ·
                refine ⟨243777184822780427949985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325036246430373903933313 243777184822780427949985)
                ·
                  refine ⟨182832888617085320962489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243777184822780427949985 182832888617085320962489)
                  ·
                    rfl

theorem cell20_400574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_400574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400574 prefixEnd_400574 := by exact prefixLift 400574
  have htrace : WordTrace (prefixWord ++ tailWord_400574) baseStart_400574 baseEnd_400574 := by
    simpa [prefixWord, tailWord_400574, baseEnd_400574] using wordTrace_append hprefix tailTrace_400574
  have hstable : (prefixWord ++ tailWord_400574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400574).length < 2 ^ (prefixWord ++ tailWord_400574).sum := by decide
  have hdescent : baseEnd_400574 < baseStart_400574 := by decide
  rcases family_descends (prefixWord ++ tailWord_400574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400575 : List Nat := [1, 1, 2, 2, 2, 2, 3, 4, 3]
def baseStart_400575 : Nat := 118140960795 + 400575 * 2 ^ 59
def prefixEnd_400575 : Nat := 4983230072969 + 3 ^ 40 * 400575 * 2
def baseEnd_400575 : Nat := 182833345044333761929151

theorem tailTrace_400575 : CollatzResearch.WordTrace tailWord_400575 prefixEnd_400575 182833345044333761929151 := by
  unfold tailWord_400575
  simp only [CollatzResearch.WordTrace]
  refine ⟨14610170523792662608491179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9740113682528441738994119 14610170523792662608491179)
  ·
    refine ⟨21915255785688993912736769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14610170523792662608491179 21915255785688993912736769)
    ·
      refine ⟨16436441839266745434552577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21915255785688993912736769 16436441839266745434552577)
      ·
        refine ⟨12327331379450059075914433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16436441839266745434552577 12327331379450059075914433)
        ·
          refine ⟨9245498534587544306935825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12327331379450059075914433 9245498534587544306935825)
          ·
            refine ⟨6934123900940658230201869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9245498534587544306935825 6934123900940658230201869)
            ·
              refine ⟨2600296462852746836325701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6934123900940658230201869 2600296462852746836325701)
              ·
                refine ⟨487555586784890031811069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2600296462852746836325701 487555586784890031811069)
                ·
                  refine ⟨182833345044333761929151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487555586784890031811069 182833345044333761929151)
                  ·
                    rfl

theorem cell20_400575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 3].length) (baseStart_400575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400575 prefixEnd_400575 := by exact prefixLift 400575
  have htrace : WordTrace (prefixWord ++ tailWord_400575) baseStart_400575 baseEnd_400575 := by
    simpa [prefixWord, tailWord_400575, baseEnd_400575] using wordTrace_append hprefix tailTrace_400575
  have hstable : (prefixWord ++ tailWord_400575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400575).length < 2 ^ (prefixWord ++ tailWord_400575).sum := by decide
  have hdescent : baseEnd_400575 < baseStart_400575 := by decide
  rcases family_descends (prefixWord ++ tailWord_400575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400616 : List Nat := [2, 1, 4, 1, 2, 1, 4, 3, 2]
def baseStart_400616 : Nat := 118140960795 + 400616 * 2 ^ 59
def prefixEnd_400616 : Nat := 4983230072969 + 3 ^ 40 * 400616 * 2
def baseEnd_400616 : Nat := 182852058561519841562317

theorem tailTrace_400616 : CollatzResearch.WordTrace tailWord_400616 prefixEnd_400616 182852058561519841562317 := by
  unfold tailWord_400616
  simp only [CollatzResearch.WordTrace]
  refine ⟨7305832958322063305366851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9741110611096084407155801 7305832958322063305366851)
  ·
    refine ⟨10958749437483094958050277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7305832958322063305366851 10958749437483094958050277)
    ·
      refine ⟨2054765519528080304634427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10958749437483094958050277 2054765519528080304634427)
      ·
        refine ⟨3082148279292120456951641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2054765519528080304634427 3082148279292120456951641)
        ·
          refine ⟨2311611209469090342713731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3082148279292120456951641 2311611209469090342713731)
          ·
            refine ⟨3467416814203635514070597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311611209469090342713731 3467416814203635514070597)
            ·
              refine ⟨650140652663181658888237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3467416814203635514070597 650140652663181658888237)
              ·
                refine ⟨243802744748693122083089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 650140652663181658888237 243802744748693122083089)
                ·
                  refine ⟨182852058561519841562317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243802744748693122083089 182852058561519841562317)
                  ·
                    rfl

theorem cell20_400616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 2].length) (baseStart_400616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400616 prefixEnd_400616 := by exact prefixLift 400616
  have htrace : WordTrace (prefixWord ++ tailWord_400616) baseStart_400616 baseEnd_400616 := by
    simpa [prefixWord, tailWord_400616, baseEnd_400616] using wordTrace_append hprefix tailTrace_400616
  have hstable : (prefixWord ++ tailWord_400616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400616).length < 2 ^ (prefixWord ++ tailWord_400616).sum := by decide
  have hdescent : baseEnd_400616 < baseStart_400616 := by decide
  rcases family_descends (prefixWord ++ tailWord_400616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400626 : List Nat := [3, 2, 1, 3, 4, 1, 1, 2, 3]
def baseStart_400626 : Nat := 118140960795 + 400626 * 2 ^ 59
def prefixEnd_400626 : Nat := 4983230072969 + 3 ^ 40 * 400626 * 2
def baseEnd_400626 : Nat := 182856622834004251228943

theorem tailTrace_400626 : CollatzResearch.WordTrace tailWord_400626 prefixEnd_400626 182856622834004251228943 := by
  unfold tailWord_400626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3653007661651974579649433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9741353764405265545731821 3653007661651974579649433)
  ·
    refine ⟨2739755746238980934737075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3653007661651974579649433 2739755746238980934737075)
    ·
      refine ⟨4109633619358471402105613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2739755746238980934737075 4109633619358471402105613)
      ·
        refine ⟨1541112607259426775789605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4109633619358471402105613 1541112607259426775789605)
        ·
          refine ⟨288958613861142520460551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1541112607259426775789605 288958613861142520460551)
          ·
            refine ⟨433437920791713780690827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288958613861142520460551 433437920791713780690827)
            ·
              refine ⟨650156881187570671036241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433437920791713780690827 650156881187570671036241)
              ·
                refine ⟨487617660890678003277181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650156881187570671036241 487617660890678003277181)
                ·
                  refine ⟨182856622834004251228943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487617660890678003277181 182856622834004251228943)
                  ·
                    rfl

theorem cell20_400626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_400626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400626 prefixEnd_400626 := by exact prefixLift 400626
  have htrace : WordTrace (prefixWord ++ tailWord_400626) baseStart_400626 baseEnd_400626 := by
    simpa [prefixWord, tailWord_400626, baseEnd_400626] using wordTrace_append hprefix tailTrace_400626
  have hstable : (prefixWord ++ tailWord_400626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400626).length < 2 ^ (prefixWord ++ tailWord_400626).sum := by decide
  have hdescent : baseEnd_400626 < baseStart_400626 := by decide
  rcases family_descends (prefixWord ++ tailWord_400626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400627 : List Nat := [1, 1, 1, 2, 2, 6, 7]
def baseStart_400627 : Nat := 118140960795 + 400627 * 2 ^ 59
def prefixEnd_400627 : Nat := 4983230072969 + 3 ^ 40 * 400627 * 2
def baseEnd_400627 : Nat := 20317453251250299132845

theorem tailTrace_400627 : CollatzResearch.WordTrace tailWord_400627 prefixEnd_400627 20317453251250299132845 := by
  unfold tailWord_400627
  simp only [CollatzResearch.WordTrace]
  refine ⟨14612067119604275489384135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9741378079736183659589423 14612067119604275489384135)
  ·
    refine ⟨21918100679406413234076203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14612067119604275489384135 21918100679406413234076203)
    ·
      refine ⟨32877151019109619851114305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21918100679406413234076203 32877151019109619851114305)
      ·
        refine ⟨24657863264332214888335729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32877151019109619851114305 24657863264332214888335729)
        ·
          refine ⟨18493397448249161166251797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24657863264332214888335729 18493397448249161166251797)
          ·
            refine ⟨866878005386679429668053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18493397448249161166251797 866878005386679429668053)
            ·
              refine ⟨20317453251250299132845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 866878005386679429668053 20317453251250299132845)
              ·
                rfl

theorem cell20_400627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 7].length) (baseStart_400627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400627 prefixEnd_400627 := by exact prefixLift 400627
  have htrace : WordTrace (prefixWord ++ tailWord_400627) baseStart_400627 baseEnd_400627 := by
    simpa [prefixWord, tailWord_400627, baseEnd_400627] using wordTrace_append hprefix tailTrace_400627
  have hstable : (prefixWord ++ tailWord_400627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400627).length < 2 ^ (prefixWord ++ tailWord_400627).sum := by decide
  have hdescent : baseEnd_400627 < baseStart_400627 := by decide
  rcases family_descends (prefixWord ++ tailWord_400627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400671 : List Nat := [1, 1, 2, 4, 4, 2, 1, 3, 2]
def baseStart_400671 : Nat := 118140960795 + 400671 * 2 ^ 59
def prefixEnd_400671 : Nat := 4983230072969 + 3 ^ 40 * 400671 * 2
def baseEnd_400671 : Nat := 182877162060184094728759

theorem tailTrace_400671 : CollatzResearch.WordTrace tailWord_400671 prefixEnd_400671 182877162060184094728759 := by
  unfold tailWord_400671
  simp only [CollatzResearch.WordTrace]
  refine ⟨14613671931444871003985867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9742447954296580669323911 14613671931444871003985867)
  ·
    refine ⟨21920507897167306505978801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14613671931444871003985867 21920507897167306505978801)
    ·
      refine ⟨16440380922875479879484101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21920507897167306505978801 16440380922875479879484101)
      ·
        refine ⟨3082571423039152477403269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16440380922875479879484101 3082571423039152477403269)
        ·
          refine ⟨577982141819841089513113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3082571423039152477403269 577982141819841089513113)
          ·
            refine ⟨433486606364880817134835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 577982141819841089513113 433486606364880817134835)
            ·
              refine ⟨650229909547321225702253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433486606364880817134835 650229909547321225702253)
              ·
                refine ⟨243836216080245459638345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 650229909547321225702253 243836216080245459638345)
                ·
                  refine ⟨182877162060184094728759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243836216080245459638345 182877162060184094728759)
                  ·
                    rfl

theorem cell20_400671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 2].length) (baseStart_400671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400671 prefixEnd_400671 := by exact prefixLift 400671
  have htrace : WordTrace (prefixWord ++ tailWord_400671) baseStart_400671 baseEnd_400671 := by
    simpa [prefixWord, tailWord_400671, baseEnd_400671] using wordTrace_append hprefix tailTrace_400671
  have hstable : (prefixWord ++ tailWord_400671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400671).length < 2 ^ (prefixWord ++ tailWord_400671).sum := by decide
  have hdescent : baseEnd_400671 < baseStart_400671 := by decide
  rcases family_descends (prefixWord ++ tailWord_400671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400682 : List Nat := [3, 1, 4, 2, 1, 1, 8]
def baseStart_400682 : Nat := 118140960795 + 400682 * 2 ^ 59
def prefixEnd_400682 : Nat := 4983230072969 + 3 ^ 40 * 400682 * 2
def baseEnd_400682 : Nat := 20320242528879660595783

theorem tailTrace_400682 : CollatzResearch.WordTrace tailWord_400682 prefixEnd_400682 20320242528879660595783 := by
  unfold tailWord_400682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3653518283601254970659075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9742715422936679921757533 3653518283601254970659075)
  ·
    refine ⟨5480277425401882455988613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3653518283601254970659075 5480277425401882455988613)
    ·
      refine ⟨1027552017262852960497865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5480277425401882455988613 1027552017262852960497865)
      ·
        refine ⟨770664012947139720373399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1027552017262852960497865 770664012947139720373399)
        ·
          refine ⟨1155996019420709580560099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770664012947139720373399 1155996019420709580560099)
          ·
            refine ⟨1733994029131064370840149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155996019420709580560099 1733994029131064370840149)
            ·
              refine ⟨20320242528879660595783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1733994029131064370840149 20320242528879660595783)
              ·
                rfl

theorem cell20_400682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 8].length) (baseStart_400682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400682 prefixEnd_400682 := by exact prefixLift 400682
  have htrace : WordTrace (prefixWord ++ tailWord_400682) baseStart_400682 baseEnd_400682 := by
    simpa [prefixWord, tailWord_400682, baseEnd_400682] using wordTrace_append hprefix tailTrace_400682
  have hstable : (prefixWord ++ tailWord_400682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400682).length < 2 ^ (prefixWord ++ tailWord_400682).sum := by decide
  have hdescent : baseEnd_400682 < baseStart_400682 := by decide
  rcases family_descends (prefixWord ++ tailWord_400682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400689 : List Nat := [1, 2, 2, 3, 3, 1, 2, 1, 5]
def baseStart_400689 : Nat := 118140960795 + 400689 * 2 ^ 59
def prefixEnd_400689 : Nat := 4983230072969 + 3 ^ 40 * 400689 * 2
def baseEnd_400689 : Nat := 182885377750656032128685

theorem tailTrace_400689 : CollatzResearch.WordTrace tailWord_400689 prefixEnd_400689 182885377750656032128685 := by
  unfold tailWord_400689
  simp only [CollatzResearch.WordTrace]
  refine ⟨14614328445379660078141121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9742885630253106718760747 14614328445379660078141121)
  ·
    refine ⟨10960746334034745058605841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14614328445379660078141121 10960746334034745058605841)
    ·
      refine ⟨8220559750526058793954381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10960746334034745058605841 8220559750526058793954381)
      ·
        refine ⟨3082709906447272047732893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8220559750526058793954381 3082709906447272047732893)
        ·
          refine ⟨1156016214917727017899835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3082709906447272047732893 1156016214917727017899835)
          ·
            refine ⟨1734024322376590526849753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156016214917727017899835 1734024322376590526849753)
            ·
              refine ⟨1300518241782442895137315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1734024322376590526849753 1300518241782442895137315)
              ·
                refine ⟨1950777362673664342705973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1300518241782442895137315 1950777362673664342705973)
                ·
                  refine ⟨182885377750656032128685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1950777362673664342705973 182885377750656032128685)
                  ·
                    rfl

theorem cell20_400689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_400689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400689 prefixEnd_400689 := by exact prefixLift 400689
  have htrace : WordTrace (prefixWord ++ tailWord_400689) baseStart_400689 baseEnd_400689 := by
    simpa [prefixWord, tailWord_400689, baseEnd_400689] using wordTrace_append hprefix tailTrace_400689
  have hstable : (prefixWord ++ tailWord_400689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400689).length < 2 ^ (prefixWord ++ tailWord_400689).sum := by decide
  have hdescent : baseEnd_400689 < baseStart_400689 := by decide
  rcases family_descends (prefixWord ++ tailWord_400689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400703 : List Nat := [1, 1, 2, 2, 4, 2, 1, 7]
def baseStart_400703 : Nat := 118140960795 + 400703 * 2 ^ 59
def prefixEnd_400703 : Nat := 4983230072969 + 3 ^ 40 * 400703 * 2
def baseEnd_400703 : Nat := 60963922577378068553987

theorem tailTrace_400703 : CollatzResearch.WordTrace tailWord_400703 prefixEnd_400703 60963922577378068553987 := by
  unfold tailWord_400703
  simp only [CollatzResearch.WordTrace]
  refine ⟨14614839067328940469150763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9743226044885960312767175 14614839067328940469150763)
  ·
    refine ⟨21922258600993410703726145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14614839067328940469150763 21922258600993410703726145)
    ·
      refine ⟨16441693950745058027794609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21922258600993410703726145 16441693950745058027794609)
      ·
        refine ⟨12331270463058793520845957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16441693950745058027794609 12331270463058793520845957)
        ·
          refine ⟨2312113211823523785158617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12331270463058793520845957 2312113211823523785158617)
          ·
            refine ⟨1734084908867642838868963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2312113211823523785158617 1734084908867642838868963)
            ·
              refine ⟨2601127363301464258303445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734084908867642838868963 2601127363301464258303445)
              ·
                refine ⟨60963922577378068553987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2601127363301464258303445 60963922577378068553987)
                ·
                  rfl

theorem cell20_400703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 7].length) (baseStart_400703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400703 prefixEnd_400703 := by exact prefixLift 400703
  have htrace : WordTrace (prefixWord ++ tailWord_400703) baseStart_400703 baseEnd_400703 := by
    simpa [prefixWord, tailWord_400703, baseEnd_400703] using wordTrace_append hprefix tailTrace_400703
  have hstable : (prefixWord ++ tailWord_400703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400703).length < 2 ^ (prefixWord ++ tailWord_400703).sum := by decide
  have hdescent : baseEnd_400703 < baseStart_400703 := by decide
  rcases family_descends (prefixWord ++ tailWord_400703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400751 : List Nat := [1, 1, 2, 1, 3, 1, 5, 4, 2]
def baseStart_400751 : Nat := 118140960795 + 400751 * 2 ^ 59
def prefixEnd_400751 : Nat := 4983230072969 + 3 ^ 40 * 400751 * 2
def baseEnd_400751 : Nat := 182913676240059372061765

theorem tailTrace_400751 : CollatzResearch.WordTrace tailWord_400751 prefixEnd_400751 182913676240059372061765 := by
  unfold tailWord_400751
  simp only [CollatzResearch.WordTrace]
  refine ⟨14616589771155044666898107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9744393180770029777932071 14616589771155044666898107)
  ·
    refine ⟨21924884656732567000347161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14616589771155044666898107 21924884656732567000347161)
    ·
      refine ⟨16443663492549425250260371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21924884656732567000347161 16443663492549425250260371)
      ·
        refine ⟨24665495238824137875390557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16443663492549425250260371 24665495238824137875390557)
        ·
          refine ⟨9249560714559051703271459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24665495238824137875390557 9249560714559051703271459)
          ·
            refine ⟨13874341071838577554907189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9249560714559051703271459 13874341071838577554907189)
            ·
              refine ⟨1300719475484866645772549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13874341071838577554907189 1300719475484866645772549)
              ·
                refine ⟨243884901653412496082353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1300719475484866645772549 243884901653412496082353)
                ·
                  refine ⟨182913676240059372061765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243884901653412496082353 182913676240059372061765)
                  ·
                    rfl

theorem cell20_400751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 2].length) (baseStart_400751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400751 prefixEnd_400751 := by exact prefixLift 400751
  have htrace : WordTrace (prefixWord ++ tailWord_400751) baseStart_400751 baseEnd_400751 := by
    simpa [prefixWord, tailWord_400751, baseEnd_400751] using wordTrace_append hprefix tailTrace_400751
  have hstable : (prefixWord ++ tailWord_400751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400751).length < 2 ^ (prefixWord ++ tailWord_400751).sum := by decide
  have hdescent : baseEnd_400751 < baseStart_400751 := by decide
  rcases family_descends (prefixWord ++ tailWord_400751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400765 : List Nat := [1, 4, 1, 1, 2, 2, 1, 5, 3]
def baseStart_400765 : Nat := 118140960795 + 400765 * 2 ^ 59
def prefixEnd_400765 : Nat := 4983230072969 + 3 ^ 40 * 400765 * 2
def baseEnd_400765 : Nat := 182920066221537545595041

theorem tailTrace_400765 : CollatzResearch.WordTrace tailWord_400765 prefixEnd_400765 182920066221537545595041 := by
  unfold tailWord_400765
  simp only [CollatzResearch.WordTrace]
  refine ⟨14617100393104325057907749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9744733595402883371938499 14617100393104325057907749)
  ·
    refine ⟨2740706323707060948357703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14617100393104325057907749 2740706323707060948357703)
    ·
      refine ⟨4111059485560591422536555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2740706323707060948357703 4111059485560591422536555)
      ·
        refine ⟨6166589228340887133804833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4111059485560591422536555 6166589228340887133804833)
        ·
          refine ⟨4624941921255665350353625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6166589228340887133804833 4624941921255665350353625)
          ·
            refine ⟨3468706440941749012765219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4624941921255665350353625 3468706440941749012765219)
            ·
              refine ⟨5203059661412623519147829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3468706440941749012765219 5203059661412623519147829)
              ·
                refine ⟨487786843257433454920109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5203059661412623519147829 487786843257433454920109)
                ·
                  refine ⟨182920066221537545595041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487786843257433454920109 182920066221537545595041)
                  ·
                    rfl

theorem cell20_400765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_400765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400765 prefixEnd_400765 := by exact prefixLift 400765
  have htrace : WordTrace (prefixWord ++ tailWord_400765) baseStart_400765 baseEnd_400765 := by
    simpa [prefixWord, tailWord_400765, baseEnd_400765] using wordTrace_append hprefix tailTrace_400765
  have hstable : (prefixWord ++ tailWord_400765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400765).length < 2 ^ (prefixWord ++ tailWord_400765).sum := by decide
  have hdescent : baseEnd_400765 < baseStart_400765 := by decide
  rcases family_descends (prefixWord ++ tailWord_400765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400772 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 6]
def baseStart_400772 : Nat := 118140960795 + 400772 * 2 ^ 59
def prefixEnd_400772 : Nat := 4983230072969 + 3 ^ 40 * 400772 * 2
def baseEnd_400772 : Nat := 182923261212276632361679

theorem tailTrace_400772 : CollatzResearch.WordTrace tailWord_400772 prefixEnd_400772 182923261212276632361679 := by
  unfold tailWord_400772
  simp only [CollatzResearch.WordTrace]
  refine ⟨7308677852039482626706285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9744903802719310168941713 7308677852039482626706285)
  ·
    refine ⟨2740754194514805985014857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7308677852039482626706285 2740754194514805985014857)
    ·
      refine ⟨2055565645886104488761143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2740754194514805985014857 2055565645886104488761143)
      ·
        refine ⟨3083348468829156733141715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2055565645886104488761143 3083348468829156733141715)
        ·
          refine ⟨4625022703243735099712573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3083348468829156733141715 4625022703243735099712573)
          ·
            refine ⟨1734383513716400662392215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4625022703243735099712573 1734383513716400662392215)
            ·
              refine ⟨2601575270574600993588323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734383513716400662392215 2601575270574600993588323)
              ·
                refine ⟨3902362905861901490382485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601575270574600993588323 3902362905861901490382485)
                ·
                  refine ⟨182923261212276632361679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3902362905861901490382485 182923261212276632361679)
                  ·
                    rfl

theorem cell20_400772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_400772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400772 prefixEnd_400772 := by exact prefixLift 400772
  have htrace : WordTrace (prefixWord ++ tailWord_400772) baseStart_400772 baseEnd_400772 := by
    simpa [prefixWord, tailWord_400772, baseEnd_400772] using wordTrace_append hprefix tailTrace_400772
  have hstable : (prefixWord ++ tailWord_400772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400772).length < 2 ^ (prefixWord ++ tailWord_400772).sum := by decide
  have hdescent : baseEnd_400772 < baseStart_400772 := by decide
  rcases family_descends (prefixWord ++ tailWord_400772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400789 : List Nat := [1, 3, 2, 1, 1, 2, 3, 5, 2]
def baseStart_400789 : Nat := 118140960795 + 400789 * 2 ^ 59
def prefixEnd_400789 : Nat := 4983230072969 + 3 ^ 40 * 400789 * 2
def baseEnd_400789 : Nat := 182931020475500128794943

theorem tailTrace_400789 : CollatzResearch.WordTrace tailWord_400789 prefixEnd_400789 182931020475500128794943 := by
  unfold tailWord_400789
  simp only [CollatzResearch.WordTrace]
  refine ⟨14617975745017377156781421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9745317163344918104520947 14617975745017377156781421)
  ·
    refine ⟨5481740904381516433793033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14617975745017377156781421 5481740904381516433793033)
    ·
      refine ⟨4111305678286137325344775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5481740904381516433793033 4111305678286137325344775)
      ·
        refine ⟨6166958517429205988017163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4111305678286137325344775 6166958517429205988017163)
        ·
          refine ⟨9250437776143808982025745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6166958517429205988017163 9250437776143808982025745)
          ·
            refine ⟨6937828332107856736519309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9250437776143808982025745 6937828332107856736519309)
            ·
              refine ⟨2601685624540446276194741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6937828332107856736519309 2601685624540446276194741)
              ·
                refine ⟨243908027300666838393257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2601685624540446276194741 243908027300666838393257)
                ·
                  refine ⟨182931020475500128794943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243908027300666838393257 182931020475500128794943)
                  ·
                    rfl

theorem cell20_400789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_400789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400789 prefixEnd_400789 := by exact prefixLift 400789
  have htrace : WordTrace (prefixWord ++ tailWord_400789) baseStart_400789 baseEnd_400789 := by
    simpa [prefixWord, tailWord_400789, baseEnd_400789] using wordTrace_append hprefix tailTrace_400789
  have hstable : (prefixWord ++ tailWord_400789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400789).length < 2 ^ (prefixWord ++ tailWord_400789).sum := by decide
  have hdescent : baseEnd_400789 < baseStart_400789 := by decide
  rcases family_descends (prefixWord ++ tailWord_400789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400817 : List Nat := [1, 2, 2, 4, 1, 1, 2, 7]
def baseStart_400817 : Nat := 118140960795 + 400817 * 2 ^ 59
def prefixEnd_400817 : Nat := 4983230072969 + 3 ^ 40 * 400817 * 2
def baseEnd_400817 : Nat := 60981266812818825287165

theorem tailTrace_400817 : CollatzResearch.WordTrace tailWord_400817 prefixEnd_400817 60981266812818825287165 := by
  unfold tailWord_400817
  simp only [CollatzResearch.WordTrace]
  refine ⟨14618996988915937938800705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9745997992610625292533803 14618996988915937938800705)
  ·
    refine ⟨10964247741686953454100529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14618996988915937938800705 10964247741686953454100529)
    ·
      refine ⟨8223185806265215090575397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10964247741686953454100529 8223185806265215090575397)
      ·
        refine ⟨1541847338674727829482887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8223185806265215090575397 1541847338674727829482887)
        ·
          refine ⟨2312771008012091744224331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1541847338674727829482887 2312771008012091744224331)
          ·
            refine ⟨3469156512018137616336497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2312771008012091744224331 3469156512018137616336497)
            ·
              refine ⟨2601867384013603212252373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3469156512018137616336497 2601867384013603212252373)
              ·
                refine ⟨60981266812818825287165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2601867384013603212252373 60981266812818825287165)
                ·
                  rfl

theorem cell20_400817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 7].length) (baseStart_400817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400817 prefixEnd_400817 := by exact prefixLift 400817
  have htrace : WordTrace (prefixWord ++ tailWord_400817) baseStart_400817 baseEnd_400817 := by
    simpa [prefixWord, tailWord_400817, baseEnd_400817] using wordTrace_append hprefix tailTrace_400817
  have hstable : (prefixWord ++ tailWord_400817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400817).length < 2 ^ (prefixWord ++ tailWord_400817).sum := by decide
  have hdescent : baseEnd_400817 < baseStart_400817 := by decide
  rcases family_descends (prefixWord ++ tailWord_400817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400844 : List Nat := [2, 2, 1, 4, 2, 1, 3, 3, 2]
def baseStart_400844 : Nat := 118140960795 + 400844 * 2 ^ 59
def prefixEnd_400844 : Nat := 4983230072969 + 3 ^ 40 * 400844 * 2
def baseEnd_400844 : Nat := 182956123974164381961385

theorem tailTrace_400844 : CollatzResearch.WordTrace tailWord_400844 prefixEnd_400844 182956123974164381961385 := by
  unfold tailWord_400844
  simp only [CollatzResearch.WordTrace]
  refine ⟨7309990879909060775016793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9746654506545414366689057 7309990879909060775016793)
  ·
    refine ⟨5482493159931795581262595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7309990879909060775016793 5482493159931795581262595)
    ·
      refine ⟨8223739739897693371893893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5482493159931795581262595 8223739739897693371893893)
      ·
        refine ⟨1541951201230817507230105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8223739739897693371893893 1541951201230817507230105)
        ·
          refine ⟨1156463400923113130422579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1541951201230817507230105 1156463400923113130422579)
          ·
            refine ⟨1734695101384669695633869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156463400923113130422579 1734695101384669695633869)
            ·
              refine ⟨650510663019251135862701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1734695101384669695633869 650510663019251135862701)
              ·
                refine ⟨243941498632219175948513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 650510663019251135862701 243941498632219175948513)
                ·
                  refine ⟨182956123974164381961385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243941498632219175948513 182956123974164381961385)
                  ·
                    rfl

theorem cell20_400844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_400844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400844 prefixEnd_400844 := by exact prefixLift 400844
  have htrace : WordTrace (prefixWord ++ tailWord_400844) baseStart_400844 baseEnd_400844 := by
    simpa [prefixWord, tailWord_400844, baseEnd_400844] using wordTrace_append hprefix tailTrace_400844
  have hstable : (prefixWord ++ tailWord_400844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400844).length < 2 ^ (prefixWord ++ tailWord_400844).sum := by decide
  have hdescent : baseEnd_400844 < baseStart_400844 := by decide
  rcases family_descends (prefixWord ++ tailWord_400844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400861 : List Nat := [1, 4, 3, 1, 1, 3, 3, 2, 2]
def baseStart_400861 : Nat := 118140960795 + 400861 * 2 ^ 59
def prefixEnd_400861 : Nat := 4983230072969 + 3 ^ 40 * 400861 * 2
def baseEnd_400861 : Nat := 182963883237387878394649

theorem tailTrace_400861 : CollatzResearch.WordTrace tailWord_400861 prefixEnd_400861 182963883237387878394649 := by
  unfold tailWord_400861
  simp only [CollatzResearch.WordTrace]
  refine ⟨14620601800756533453402437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9747067867171022302268291 14620601800756533453402437)
  ·
    refine ⟨2741362837641850022512957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14620601800756533453402437 2741362837641850022512957)
    ·
      refine ⟨1028011064115693758442359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2741362837641850022512957 1028011064115693758442359)
      ·
        refine ⟨1542016596173540637663539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1028011064115693758442359 1542016596173540637663539)
        ·
          refine ⟨2313024894260310956495309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542016596173540637663539 2313024894260310956495309)
          ·
            refine ⟨867384335347616608685741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2313024894260310956495309 867384335347616608685741)
            ·
              refine ⟨325269125755356228257153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 867384335347616608685741 325269125755356228257153)
              ·
                refine ⟨243951844316517171192865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325269125755356228257153 243951844316517171192865)
                ·
                  refine ⟨182963883237387878394649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243951844316517171192865 182963883237387878394649)
                  ·
                    rfl

theorem cell20_400861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_400861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400861 prefixEnd_400861 := by exact prefixLift 400861
  have htrace : WordTrace (prefixWord ++ tailWord_400861) baseStart_400861 baseEnd_400861 := by
    simpa [prefixWord, tailWord_400861, baseEnd_400861] using wordTrace_append hprefix tailTrace_400861
  have hstable : (prefixWord ++ tailWord_400861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400861).length < 2 ^ (prefixWord ++ tailWord_400861).sum := by decide
  have hdescent : baseEnd_400861 < baseStart_400861 := by decide
  rcases family_descends (prefixWord ++ tailWord_400861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400865 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 4]
def baseStart_400865 : Nat := 118140960795 + 400865 * 2 ^ 59
def prefixEnd_400865 : Nat := 4983230072969 + 3 ^ 40 * 400865 * 2
def baseEnd_400865 : Nat := 182965708946381642261299

theorem tailTrace_400865 : CollatzResearch.WordTrace tailWord_400865 prefixEnd_400865 182965708946381642261299 := by
  unfold tailWord_400865
  simp only [CollatzResearch.WordTrace]
  refine ⟨14620747692742042136548049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9747165128494694757698699 14620747692742042136548049)
  ·
    refine ⟨10965560769556531602411037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14620747692742042136548049 10965560769556531602411037)
    ·
      refine ⟨4112085288583699350904139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10965560769556531602411037 4112085288583699350904139)
      ·
        refine ⟨6168127932875549026356209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4112085288583699350904139 6168127932875549026356209)
        ·
          refine ⟨4626095949656661769767157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6168127932875549026356209 4626095949656661769767157)
          ·
            refine ⟨433696495280312040915671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4626095949656661769767157 433696495280312040915671)
            ·
              refine ⟨650544742920468061373507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433696495280312040915671 650544742920468061373507)
              ·
                refine ⟨975817114380702092060261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650544742920468061373507 975817114380702092060261)
                ·
                  refine ⟨182965708946381642261299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 975817114380702092060261 182965708946381642261299)
                  ·
                    rfl

theorem cell20_400865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_400865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400865 prefixEnd_400865 := by exact prefixLift 400865
  have htrace : WordTrace (prefixWord ++ tailWord_400865) baseStart_400865 baseEnd_400865 := by
    simpa [prefixWord, tailWord_400865, baseEnd_400865] using wordTrace_append hprefix tailTrace_400865
  have hstable : (prefixWord ++ tailWord_400865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400865).length < 2 ^ (prefixWord ++ tailWord_400865).sum := by decide
  have hdescent : baseEnd_400865 < baseStart_400865 := by decide
  rcases family_descends (prefixWord ++ tailWord_400865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400893 : List Nat := [1, 4, 1, 1, 1, 4, 2, 6]
def baseStart_400893 : Nat := 118140960795 + 400893 * 2 ^ 59
def prefixEnd_400893 : Nat := 4983230072969 + 3 ^ 40 * 400893 * 2
def baseEnd_400893 : Nat := 60992829636445996442617

theorem tailTrace_400893 : CollatzResearch.WordTrace tailWord_400893 prefixEnd_400893 60992829636445996442617 := by
  unfold tailWord_400893
  simp only [CollatzResearch.WordTrace]
  refine ⟨14621768936640602918567333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9747845957760401945711555 14621768936640602918567333)
  ·
    refine ⟨2741581675620113047231375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14621768936640602918567333 2741581675620113047231375)
    ·
      refine ⟨4112372513430169570847063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2741581675620113047231375 4112372513430169570847063)
      ·
        refine ⟨6168558770145254356270595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4112372513430169570847063 6168558770145254356270595)
        ·
          refine ⟨9252838155217881534405893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6168558770145254356270595 9252838155217881534405893)
          ·
            refine ⟨1734907154103352787701105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9252838155217881534405893 1734907154103352787701105)
            ·
              refine ⟨1301180365577514590775829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1734907154103352787701105 1301180365577514590775829)
              ·
                refine ⟨60992829636445996442617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1301180365577514590775829 60992829636445996442617)
                ·
                  rfl

theorem cell20_400893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 6].length) (baseStart_400893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400893 prefixEnd_400893 := by exact prefixLift 400893
  have htrace : WordTrace (prefixWord ++ tailWord_400893) baseStart_400893 baseEnd_400893 := by
    simpa [prefixWord, tailWord_400893, baseEnd_400893] using wordTrace_append hprefix tailTrace_400893
  have hstable : (prefixWord ++ tailWord_400893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400893).length < 2 ^ (prefixWord ++ tailWord_400893).sum := by decide
  have hdescent : baseEnd_400893 < baseStart_400893 := by decide
  rcases family_descends (prefixWord ++ tailWord_400893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400910 : List Nat := [4, 1, 1, 2, 5, 7]
def baseStart_400910 : Nat := 118140960795 + 400910 * 2 ^ 59
def prefixEnd_400910 : Nat := 4983230072969 + 3 ^ 40 * 400910 * 2
def baseEnd_400910 : Nat := 6777268450835610583745

theorem tailTrace_400910 : CollatzResearch.WordTrace tailWord_400910 prefixEnd_400910 6777268450835610583745 := by
  unfold tailWord_400910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1827798622197376852742023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9748259318386009881290789 1827798622197376852742023)
  ·
    refine ⟨2741697933296065279113035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1827798622197376852742023 2741697933296065279113035)
    ·
      refine ⟨4112546899944097918669553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2741697933296065279113035 4112546899944097918669553)
      ·
        refine ⟨3084410174958073439002165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4112546899944097918669553 3084410174958073439002165)
        ·
          refine ⟨289163453902319384906453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3084410174958073439002165 289163453902319384906453)
          ·
            refine ⟨6777268450835610583745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 289163453902319384906453 6777268450835610583745)
            ·
              rfl

theorem cell20_400910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 7].length) (baseStart_400910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400910 prefixEnd_400910 := by exact prefixLift 400910
  have htrace : WordTrace (prefixWord ++ tailWord_400910) baseStart_400910 baseEnd_400910 := by
    simpa [prefixWord, tailWord_400910, baseEnd_400910] using wordTrace_append hprefix tailTrace_400910
  have hstable : (prefixWord ++ tailWord_400910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400910).length < 2 ^ (prefixWord ++ tailWord_400910).sum := by decide
  have hdescent : baseEnd_400910 < baseStart_400910 := by decide
  rcases family_descends (prefixWord ++ tailWord_400910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400917 : List Nat := [1, 3, 2, 1, 3, 2, 1, 4, 3]
def baseStart_400917 : Nat := 118140960795 + 400917 * 2 ^ 59
def prefixEnd_400917 : Nat := 4983230072969 + 3 ^ 40 * 400917 * 2
def baseEnd_400917 : Nat := 182989443163300572527753

theorem tailTrace_400917 : CollatzResearch.WordTrace tailWord_400917 prefixEnd_400917 182989443163300572527753 := by
  unfold tailWord_400917
  simp only [CollatzResearch.WordTrace]
  refine ⟨14622644288553655017441005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9748429525702436678294003 14622644288553655017441005)
  ·
    refine ⟨5483491608207620631540377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14622644288553655017441005 5483491608207620631540377)
    ·
      refine ⟨4112618706155715473655283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5483491608207620631540377 4112618706155715473655283)
      ·
        refine ⟨6168928059233573210482925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4112618706155715473655283 6168928059233573210482925)
        ·
          refine ⟨2313348022212589953931097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6168928059233573210482925 2313348022212589953931097)
          ·
            refine ⟨1735011016659442465448323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2313348022212589953931097 1735011016659442465448323)
            ·
              refine ⟨2602516524989163698172485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1735011016659442465448323 2602516524989163698172485)
              ·
                refine ⟨487971848435468193407341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2602516524989163698172485 487971848435468193407341)
                ·
                  refine ⟨182989443163300572527753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487971848435468193407341 182989443163300572527753)
                  ·
                    rfl

theorem cell20_400917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_400917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400917 prefixEnd_400917 := by exact prefixLift 400917
  have htrace : WordTrace (prefixWord ++ tailWord_400917) baseStart_400917 baseEnd_400917 := by
    simpa [prefixWord, tailWord_400917, baseEnd_400917] using wordTrace_append hprefix tailTrace_400917
  have hstable : (prefixWord ++ tailWord_400917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400917).length < 2 ^ (prefixWord ++ tailWord_400917).sum := by decide
  have hdescent : baseEnd_400917 < baseStart_400917 := by decide
  rcases family_descends (prefixWord ++ tailWord_400917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400920 : List Nat := [2, 1, 2, 3, 4, 1, 1, 4, 2]
def baseStart_400920 : Nat := 118140960795 + 400920 * 2 ^ 59
def prefixEnd_400920 : Nat := 4983230072969 + 3 ^ 40 * 400920 * 2
def baseEnd_400920 : Nat := 182990812445045895427741

theorem tailTrace_400920 : CollatzResearch.WordTrace tailWord_400920 prefixEnd_400920 182990812445045895427741 := by
  unfold tailWord_400920
  simp only [CollatzResearch.WordTrace]
  refine ⟨7311376853771393264900107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9748502471695191019866809 7311376853771393264900107)
  ·
    refine ⟨10967065280657089897350161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7311376853771393264900107 10967065280657089897350161)
    ·
      refine ⟨8225298960492817423012621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10967065280657089897350161 8225298960492817423012621)
      ·
        refine ⟨3084487110184806533629733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8225298960492817423012621 3084487110184806533629733)
        ·
          refine ⟨578341333159651225055575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3084487110184806533629733 578341333159651225055575)
          ·
            refine ⟨867511999739476837583363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578341333159651225055575 867511999739476837583363)
            ·
              refine ⟨1301267999609215256375045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867511999739476837583363 1301267999609215256375045)
              ·
                refine ⟨243987749926727860570321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1301267999609215256375045 243987749926727860570321)
                ·
                  refine ⟨182990812445045895427741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243987749926727860570321 182990812445045895427741)
                  ·
                    rfl

theorem cell20_400920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 4, 2].length) (baseStart_400920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400920 prefixEnd_400920 := by exact prefixLift 400920
  have htrace : WordTrace (prefixWord ++ tailWord_400920) baseStart_400920 baseEnd_400920 := by
    simpa [prefixWord, tailWord_400920, baseEnd_400920] using wordTrace_append hprefix tailTrace_400920
  have hstable : (prefixWord ++ tailWord_400920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400920).length < 2 ^ (prefixWord ++ tailWord_400920).sum := by decide
  have hdescent : baseEnd_400920 < baseStart_400920 := by decide
  rcases family_descends (prefixWord ++ tailWord_400920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400924 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 4]
def baseStart_400924 : Nat := 118140960795 + 400924 * 2 ^ 59
def prefixEnd_400924 : Nat := 4983230072969 + 3 ^ 40 * 400924 * 2
def baseEnd_400924 : Nat := 182992638154039659294391

theorem tailTrace_400924 : CollatzResearch.WordTrace tailWord_400924 prefixEnd_400924 182992638154039659294391 := by
  unfold tailWord_400924
  simp only [CollatzResearch.WordTrace]
  refine ⟨7311449799764147606472913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9748599733018863475297217 7311449799764147606472913)
  ·
    refine ⟨5483587349823110704854685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7311449799764147606472913 5483587349823110704854685)
    ·
      refine ⟨2056345256183666514320507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5483587349823110704854685 2056345256183666514320507)
      ·
        refine ⟨3084517884275499771480761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2056345256183666514320507 3084517884275499771480761)
        ·
          refine ⟨2313388413206624828610571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3084517884275499771480761 2313388413206624828610571)
          ·
            refine ⟨3470082619809937242915857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313388413206624828610571 3470082619809937242915857)
            ·
              refine ⟨2602561964857452932186893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3470082619809937242915857 2602561964857452932186893)
              ·
                refine ⟨975960736821544849570085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2602561964857452932186893 975960736821544849570085)
                ·
                  refine ⟨182992638154039659294391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 975960736821544849570085 182992638154039659294391)
                  ·
                    rfl

theorem cell20_400924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_400924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400924 prefixEnd_400924 := by exact prefixLift 400924
  have htrace : WordTrace (prefixWord ++ tailWord_400924) baseStart_400924 baseEnd_400924 := by
    simpa [prefixWord, tailWord_400924, baseEnd_400924] using wordTrace_append hprefix tailTrace_400924
  have hstable : (prefixWord ++ tailWord_400924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400924).length < 2 ^ (prefixWord ++ tailWord_400924).sum := by decide
  have hdescent : baseEnd_400924 < baseStart_400924 := by decide
  rcases family_descends (prefixWord ++ tailWord_400924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400972 : List Nat := [2, 2, 1, 3, 1, 5, 1, 2, 3]
def baseStart_400972 : Nat := 118140960795 + 400972 * 2 ^ 59
def prefixEnd_400972 : Nat := 4983230072969 + 3 ^ 40 * 400972 * 2
def baseEnd_400972 : Nat := 183014546661964825694195

theorem tailTrace_400972 : CollatzResearch.WordTrace tailWord_400972 prefixEnd_400972 183014546661964825694195 := by
  unfold tailWord_400972
  simp only [CollatzResearch.WordTrace]
  refine ⟨7312325151677199705346585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9749766868902932940462113 7312325151677199705346585)
  ·
    refine ⟨5484243863757899779009939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7312325151677199705346585 5484243863757899779009939)
    ·
      refine ⟨8226365795636849668514909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5484243863757899779009939 8226365795636849668514909)
      ·
        refine ⟨3084887173363818625693091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8226365795636849668514909 3084887173363818625693091)
        ·
          refine ⟨4627330760045727938539637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3084887173363818625693091 4627330760045727938539637)
          ·
            refine ⟨433812258754286994238091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4627330760045727938539637 433812258754286994238091)
            ·
              refine ⟨650718388131430491357137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433812258754286994238091 650718388131430491357137)
              ·
                refine ⟨488038791098572868517853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650718388131430491357137 488038791098572868517853)
                ·
                  refine ⟨183014546661964825694195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488038791098572868517853 183014546661964825694195)
                  ·
                    rfl

theorem cell20_400972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_400972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400972 prefixEnd_400972 := by exact prefixLift 400972
  have htrace : WordTrace (prefixWord ++ tailWord_400972) baseStart_400972 baseEnd_400972 := by
    simpa [prefixWord, tailWord_400972, baseEnd_400972] using wordTrace_append hprefix tailTrace_400972
  have hstable : (prefixWord ++ tailWord_400972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400972).length < 2 ^ (prefixWord ++ tailWord_400972).sum := by decide
  have hdescent : baseEnd_400972 < baseStart_400972 := by decide
  rcases family_descends (prefixWord ++ tailWord_400972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_400976 : List Nat := [2, 1, 1, 1, 1, 3, 5, 1, 5]
def baseStart_400976 : Nat := 118140960795 + 400976 * 2 ^ 59
def prefixEnd_400976 : Nat := 4983230072969 + 3 ^ 40 * 400976 * 2
def baseEnd_400976 : Nat := 183016372370958589560845

theorem tailTrace_400976 : CollatzResearch.WordTrace tailWord_400976 prefixEnd_400976 183016372370958589560845 := by
  unfold tailWord_400976
  simp only [CollatzResearch.WordTrace]
  refine ⟨7312398097669954046919391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9749864130226605395892521 7312398097669954046919391)
  ·
    refine ⟨10968597146504931070379087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7312398097669954046919391 10968597146504931070379087)
    ·
      refine ⟨16452895719757396605568631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10968597146504931070379087 16452895719757396605568631)
      ·
        refine ⟨24679343579636094908352947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16452895719757396605568631 24679343579636094908352947)
        ·
          refine ⟨37019015369454142362529421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24679343579636094908352947 37019015369454142362529421)
          ·
            refine ⟨13882130763545303385948533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37019015369454142362529421 13882130763545303385948533)
            ·
              refine ⟨1301449759082372192432675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13882130763545303385948533 1301449759082372192432675)
              ·
                refine ⟨1952174638623558288649013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1301449759082372192432675 1952174638623558288649013)
                ·
                  refine ⟨183016372370958589560845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1952174638623558288649013 183016372370958589560845)
                  ·
                    rfl

theorem cell20_400976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_400976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_400976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_400976 prefixEnd_400976 := by exact prefixLift 400976
  have htrace : WordTrace (prefixWord ++ tailWord_400976) baseStart_400976 baseEnd_400976 := by
    simpa [prefixWord, tailWord_400976, baseEnd_400976] using wordTrace_append hprefix tailTrace_400976
  have hstable : (prefixWord ++ tailWord_400976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_400976).length < 2 ^ (prefixWord ++ tailWord_400976).sum := by decide
  have hdescent : baseEnd_400976 < baseStart_400976 := by decide
  rcases family_descends (prefixWord ++ tailWord_400976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401013 : List Nat := [1, 3, 4, 2, 1, 3, 1, 3, 2]
def baseStart_401013 : Nat := 118140960795 + 401013 * 2 ^ 59
def prefixEnd_401013 : Nat := 4983230072969 + 3 ^ 40 * 401013 * 2
def baseEnd_401013 : Nat := 183033260179150905327361

theorem tailTrace_401013 : CollatzResearch.WordTrace tailWord_401013 prefixEnd_401013 183033260179150905327361 := by
  unfold tailWord_401013
  simp only [CollatzResearch.WordTrace]
  refine ⟨14626145696205863412935693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9750763797470575608623795 14626145696205863412935693)
  ·
    refine ⟨5484804636077198779850885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14626145696205863412935693 5484804636077198779850885)
    ·
      refine ⟨1028400869264474771222041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5484804636077198779850885 1028400869264474771222041)
      ·
        refine ⟨771300651948356078416531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1028400869264474771222041 771300651948356078416531)
        ·
          refine ⟨1156950977922534117624797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771300651948356078416531 1156950977922534117624797)
          ·
            refine ⟨433856616720950294109299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1156950977922534117624797 433856616720950294109299)
            ·
              refine ⟨650784925081425441163949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433856616720950294109299 650784925081425441163949)
              ·
                refine ⟨244044346905534540436481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 650784925081425441163949 244044346905534540436481)
                ·
                  refine ⟨183033260179150905327361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244044346905534540436481 183033260179150905327361)
                  ·
                    rfl

theorem cell20_401013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_401013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401013 prefixEnd_401013 := by exact prefixLift 401013
  have htrace : WordTrace (prefixWord ++ tailWord_401013) baseStart_401013 baseEnd_401013 := by
    simpa [prefixWord, tailWord_401013, baseEnd_401013] using wordTrace_append hprefix tailTrace_401013
  have hstable : (prefixWord ++ tailWord_401013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401013).length < 2 ^ (prefixWord ++ tailWord_401013).sum := by decide
  have hdescent : baseEnd_401013 < baseStart_401013 := by decide
  rcases family_descends (prefixWord ++ tailWord_401013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401044 : List Nat := [2, 4, 2, 2, 2, 2, 2, 1, 3]
def baseStart_401044 : Nat := 118140960795 + 401044 * 2 ^ 59
def prefixEnd_401044 : Nat := 4983230072969 + 3 ^ 40 * 401044 * 2
def baseEnd_401044 : Nat := 183047409423852575293901

theorem tailTrace_401044 : CollatzResearch.WordTrace tailWord_401044 prefixEnd_401044 183047409423852575293901 := by
  unfold tailWord_401044
  simp only [CollatzResearch.WordTrace]
  refine ⟨7313638179546777853657093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9751517572729037138209457 7313638179546777853657093)
  ·
    refine ⟨1371307158665020847560705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7313638179546777853657093 1371307158665020847560705)
    ·
      refine ⟨1028480368998765635670529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1371307158665020847560705 1028480368998765635670529)
      ·
        refine ⟨771360276749074226752897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1028480368998765635670529 771360276749074226752897)
        ·
          refine ⟨578520207561805670064673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771360276749074226752897 578520207561805670064673)
          ·
            refine ⟨433890155671354252548505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578520207561805670064673 433890155671354252548505)
            ·
              refine ⟨325417616753515689411379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433890155671354252548505 325417616753515689411379)
              ·
                refine ⟨488126425130273534117069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325417616753515689411379 488126425130273534117069)
                ·
                  refine ⟨183047409423852575293901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488126425130273534117069 183047409423852575293901)
                  ·
                    rfl

theorem cell20_401044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_401044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401044 prefixEnd_401044 := by exact prefixLift 401044
  have htrace : WordTrace (prefixWord ++ tailWord_401044) baseStart_401044 baseEnd_401044 := by
    simpa [prefixWord, tailWord_401044, baseEnd_401044] using wordTrace_append hprefix tailTrace_401044
  have hstable : (prefixWord ++ tailWord_401044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401044).length < 2 ^ (prefixWord ++ tailWord_401044).sum := by decide
  have hdescent : baseEnd_401044 < baseStart_401044 := by decide
  rcases family_descends (prefixWord ++ tailWord_401044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401048 : List Nat := [2, 1, 2, 4, 1, 2, 4, 1, 3]
def baseStart_401048 : Nat := 118140960795 + 401048 * 2 ^ 59
def prefixEnd_401048 : Nat := 4983230072969 + 3 ^ 40 * 401048 * 2
def baseEnd_401048 : Nat := 183049235132846339160551

theorem tailTrace_401048 : CollatzResearch.WordTrace tailWord_401048 prefixEnd_401048 183049235132846339160551 := by
  unfold tailWord_401048
  simp only [CollatzResearch.WordTrace]
  refine ⟨7313711125539532195229899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9751614834052709593639865 7313711125539532195229899)
  ·
    refine ⟨10970566688309298292844849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7313711125539532195229899 10970566688309298292844849)
    ·
      refine ⟨8227925016231973719633637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10970566688309298292844849 8227925016231973719633637)
      ·
        refine ⟨1542735940543495072431307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8227925016231973719633637 1542735940543495072431307)
        ·
          refine ⟨2314103910815242608646961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542735940543495072431307 2314103910815242608646961)
          ·
            refine ⟨1735577933111431956485221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2314103910815242608646961 1735577933111431956485221)
            ·
              refine ⟨325420862458393491840979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1735577933111431956485221 325420862458393491840979)
              ·
                refine ⟨488131293687590237761469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325420862458393491840979 488131293687590237761469)
                ·
                  refine ⟨183049235132846339160551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488131293687590237761469 183049235132846339160551)
                  ·
                    rfl

theorem cell20_401048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_401048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401048 prefixEnd_401048 := by exact prefixLift 401048
  have htrace : WordTrace (prefixWord ++ tailWord_401048) baseStart_401048 baseEnd_401048 := by
    simpa [prefixWord, tailWord_401048, baseEnd_401048] using wordTrace_append hprefix tailTrace_401048
  have hstable : (prefixWord ++ tailWord_401048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401048).length < 2 ^ (prefixWord ++ tailWord_401048).sum := by decide
  have hdescent : baseEnd_401048 < baseStart_401048 := by decide
  rcases family_descends (prefixWord ++ tailWord_401048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401059 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 6]
def baseStart_401059 : Nat := 118140960795 + 401059 * 2 ^ 59
def prefixEnd_401059 : Nat := 4983230072969 + 3 ^ 40 * 401059 * 2
def baseEnd_401059 : Nat := 183054255832579189793839

theorem tailTrace_401059 : CollatzResearch.WordTrace tailWord_401059 prefixEnd_401059 183054255832579189793839 := by
  unfold tailWord_401059
  simp only [CollatzResearch.WordTrace]
  refine ⟨14627823454039213269110231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9751882302692808846073487 14627823454039213269110231)
  ·
    refine ⟨21941735181058819903665347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14627823454039213269110231 21941735181058819903665347)
    ·
      refine ⟨32912602771588229855498021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21941735181058819903665347 32912602771588229855498021)
      ·
        refine ⟨6171113019672793097905879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32912602771588229855498021 6171113019672793097905879)
        ·
          refine ⟨9256669529509189646858819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6171113019672793097905879 9256669529509189646858819)
          ·
            refine ⟨13885004294263784470288229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9256669529509189646858819 13885004294263784470288229)
            ·
              refine ⟨2603438305174459588179043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13885004294263784470288229 2603438305174459588179043)
              ·
                refine ⟨3905157457761689382268565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603438305174459588179043 3905157457761689382268565)
                ·
                  refine ⟨183054255832579189793839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3905157457761689382268565 183054255832579189793839)
                  ·
                    rfl

theorem cell20_401059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_401059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401059 prefixEnd_401059 := by exact prefixLift 401059
  have htrace : WordTrace (prefixWord ++ tailWord_401059) baseStart_401059 baseEnd_401059 := by
    simpa [prefixWord, tailWord_401059, baseEnd_401059] using wordTrace_append hprefix tailTrace_401059
  have hstable : (prefixWord ++ tailWord_401059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401059).length < 2 ^ (prefixWord ++ tailWord_401059).sum := by decide
  have hdescent : baseEnd_401059 < baseStart_401059 := by decide
  rcases family_descends (prefixWord ++ tailWord_401059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401086 : List Nat := [4, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_401086 : Nat := 118140960795 + 401086 * 2 ^ 59
def prefixEnd_401086 : Nat := 4983230072969 + 3 ^ 40 * 401086 * 2
def baseEnd_401086 : Nat := 183066579368287095893729

theorem tailTrace_401086 : CollatzResearch.WordTrace tailWord_401086 prefixEnd_401086 183066579368287095893729 := by
  unfold tailWord_401086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1828601028117674610042889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9752538816627597920228741 1828601028117674610042889)
  ·
    refine ⟨1371450771088255957532167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1828601028117674610042889 1371450771088255957532167)
    ·
      refine ⟨2057176156632383936298251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1371450771088255957532167 2057176156632383936298251)
      ·
        refine ⟨3085764234948575904447377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2057176156632383936298251 3085764234948575904447377)
        ·
          refine ⟨2314323176211431928335533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3085764234948575904447377 2314323176211431928335533)
          ·
            refine ⟨867871191079286973125825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2314323176211431928335533 867871191079286973125825)
            ·
              refine ⟨650903393309465229844369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867871191079286973125825 650903393309465229844369)
              ·
                refine ⟨488177544982098922383277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650903393309465229844369 488177544982098922383277)
                ·
                  refine ⟨183066579368287095893729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488177544982098922383277 183066579368287095893729)
                  ·
                    rfl

theorem cell20_401086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_401086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401086 prefixEnd_401086 := by exact prefixLift 401086
  have htrace : WordTrace (prefixWord ++ tailWord_401086) baseStart_401086 baseEnd_401086 := by
    simpa [prefixWord, tailWord_401086, baseEnd_401086] using wordTrace_append hprefix tailTrace_401086
  have hstable : (prefixWord ++ tailWord_401086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401086).length < 2 ^ (prefixWord ++ tailWord_401086).sum := by decide
  have hdescent : baseEnd_401086 < baseStart_401086 := by decide
  rcases family_descends (prefixWord ++ tailWord_401086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401104 : List Nat := [2, 1, 1, 1, 1, 2, 1, 11]
def baseStart_401104 : Nat := 118140960795 + 401104 * 2 ^ 59
def prefixEnd_401104 : Nat := 4983230072969 + 3 ^ 40 * 401104 * 2
def baseEnd_401104 : Nat := 61024931686253011097885

theorem tailTrace_401104 : CollatzResearch.WordTrace tailWord_401104 prefixEnd_401104 61024931686253011097885 := by
  unfold tailWord_401104
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314732369438092977249183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9752976492584123969665577 7314732369438092977249183)
  ·
    refine ⟨10972098554157139465873775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7314732369438092977249183 10972098554157139465873775)
    ·
      refine ⟨16458147831235709198810663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10972098554157139465873775 16458147831235709198810663)
      ·
        refine ⟨24687221746853563798215995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16458147831235709198810663 24687221746853563798215995)
        ·
          refine ⟨37030832620280345697323993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24687221746853563798215995 37030832620280345697323993)
          ·
            refine ⟨27773124465210259272992995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37030832620280345697323993 27773124465210259272992995)
            ·
              refine ⟨41659686697815388909489493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27773124465210259272992995 41659686697815388909489493)
              ·
                refine ⟨61024931686253011097885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 41659686697815388909489493 61024931686253011097885)
                ·
                  rfl

theorem cell20_401104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_401104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401104 prefixEnd_401104 := by exact prefixLift 401104
  have htrace : WordTrace (prefixWord ++ tailWord_401104) baseStart_401104 baseEnd_401104 := by
    simpa [prefixWord, tailWord_401104, baseEnd_401104] using wordTrace_append hprefix tailTrace_401104
  have hstable : (prefixWord ++ tailWord_401104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401104).length < 2 ^ (prefixWord ++ tailWord_401104).sum := by decide
  have hdescent : baseEnd_401104 < baseStart_401104 := by decide
  rcases family_descends (prefixWord ++ tailWord_401104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401114 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_401114 : Nat := 118140960795 + 401114 * 2 ^ 59
def prefixEnd_401114 : Nat := 4983230072969 + 3 ^ 40 * 401114 * 2
def baseEnd_401114 : Nat := 183079359331243442960281

theorem tailTrace_401114 : CollatzResearch.WordTrace tailWord_401114 prefixEnd_401114 183079359331243442960281 := by
  unfold tailWord_401114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3657457367209989415590599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9753219645893305108241597 3657457367209989415590599)
  ·
    refine ⟨5486186050814984123385899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3657457367209989415590599 5486186050814984123385899)
    ·
      refine ⟨8229279076222476185078849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5486186050814984123385899 8229279076222476185078849)
      ·
        refine ⟨6171959307166857138809137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8229279076222476185078849 6171959307166857138809137)
        ·
          refine ⟨4628969480375142854106853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6171959307166857138809137 4628969480375142854106853)
          ·
            refine ⟨867931777570339285145035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4628969480375142854106853 867931777570339285145035)
            ·
              refine ⟨1301897666355508927717553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867931777570339285145035 1301897666355508927717553)
              ·
                refine ⟨976423249766631695788165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1301897666355508927717553 976423249766631695788165)
                ·
                  refine ⟨183079359331243442960281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 976423249766631695788165 183079359331243442960281)
                  ·
                    rfl

theorem cell20_401114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_401114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401114 prefixEnd_401114 := by exact prefixLift 401114
  have htrace : WordTrace (prefixWord ++ tailWord_401114) baseStart_401114 baseEnd_401114 := by
    simpa [prefixWord, tailWord_401114, baseEnd_401114] using wordTrace_append hprefix tailTrace_401114
  have hstable : (prefixWord ++ tailWord_401114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401114).length < 2 ^ (prefixWord ++ tailWord_401114).sum := by decide
  have hdescent : baseEnd_401114 < baseStart_401114 := by decide
  rcases family_descends (prefixWord ++ tailWord_401114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401127 : List Nat := [1, 1, 5, 4, 1, 1, 2, 3, 2]
def baseStart_401127 : Nat := 118140960795 + 401127 * 2 ^ 59
def prefixEnd_401127 : Nat := 4983230072969 + 3 ^ 40 * 401127 * 2
def baseEnd_401127 : Nat := 183085292885473175526895

theorem tailTrace_401127 : CollatzResearch.WordTrace tailWord_401127 prefixEnd_401127 183085292885473175526895 := by
  unfold tailWord_401127
  simp only [CollatzResearch.WordTrace]
  refine ⟨14630303617792860882585635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9753535745195240588390423 14630303617792860882585635)
  ·
    refine ⟨21945455426689291323878453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14630303617792860882585635 21945455426689291323878453)
    ·
      refine ⟨2057386446252121061613605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21945455426689291323878453 2057386446252121061613605)
      ·
        refine ⟨385759958672272699052551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2057386446252121061613605 385759958672272699052551)
        ·
          refine ⟨578639938008409048578827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385759958672272699052551 578639938008409048578827)
          ·
            refine ⟨867959907012613572868241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578639938008409048578827 867959907012613572868241)
            ·
              refine ⟨650969930259460179651181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867959907012613572868241 650969930259460179651181)
              ·
                refine ⟨244113723847297567369193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 650969930259460179651181 244113723847297567369193)
                ·
                  refine ⟨183085292885473175526895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244113723847297567369193 183085292885473175526895)
                  ·
                    rfl

theorem cell20_401127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 3, 2].length) (baseStart_401127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401127 prefixEnd_401127 := by exact prefixLift 401127
  have htrace : WordTrace (prefixWord ++ tailWord_401127) baseStart_401127 baseEnd_401127 := by
    simpa [prefixWord, tailWord_401127, baseEnd_401127] using wordTrace_append hprefix tailTrace_401127
  have hstable : (prefixWord ++ tailWord_401127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401127).length < 2 ^ (prefixWord ++ tailWord_401127).sum := by decide
  have hdescent : baseEnd_401127 < baseStart_401127 := by decide
  rcases family_descends (prefixWord ++ tailWord_401127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401135 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 6]
def baseStart_401135 : Nat := 118140960795 + 401135 * 2 ^ 59
def prefixEnd_401135 : Nat := 4983230072969 + 3 ^ 40 * 401135 * 2
def baseEnd_401135 : Nat := 183088944303460703260195

theorem tailTrace_401135 : CollatzResearch.WordTrace tailWord_401135 prefixEnd_401135 183088944303460703260195 := by
  unfold tailWord_401135
  simp only [CollatzResearch.WordTrace]
  refine ⟨14630595401763878248876859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9753730267842585499251239 14630595401763878248876859)
  ·
    refine ⟨21945893102645817373315289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14630595401763878248876859 21945893102645817373315289)
    ·
      refine ⟨16459419826984363029986467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21945893102645817373315289 16459419826984363029986467)
      ·
        refine ⟨24689129740476544544979701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16459419826984363029986467 24689129740476544544979701)
        ·
          refine ⟨2314605913169676051091847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24689129740476544544979701 2314605913169676051091847)
          ·
            refine ⟨3471908869754514076637771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2314605913169676051091847 3471908869754514076637771)
            ·
              refine ⟨5207863304631771114956657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3471908869754514076637771 5207863304631771114956657)
              ·
                refine ⟨3905897478473828336217493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5207863304631771114956657 3905897478473828336217493)
                ·
                  refine ⟨183088944303460703260195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3905897478473828336217493 183088944303460703260195)
                  ·
                    rfl

theorem cell20_401135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_401135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401135 prefixEnd_401135 := by exact prefixLift 401135
  have htrace : WordTrace (prefixWord ++ tailWord_401135) baseStart_401135 baseEnd_401135 := by
    simpa [prefixWord, tailWord_401135, baseEnd_401135] using wordTrace_append hprefix tailTrace_401135
  have hstable : (prefixWord ++ tailWord_401135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401135).length < 2 ^ (prefixWord ++ tailWord_401135).sum := by decide
  have hdescent : baseEnd_401135 < baseStart_401135 := by decide
  rcases family_descends (prefixWord ++ tailWord_401135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401162 : List Nat := [3, 1, 2, 2, 1, 4, 3, 1, 3]
def baseStart_401162 : Nat := 118140960795 + 401162 * 2 ^ 59
def prefixEnd_401162 : Nat := 4983230072969 + 3 ^ 40 * 401162 * 2
def baseEnd_401162 : Nat := 183101267839168609360085

theorem tailTrace_401162 : CollatzResearch.WordTrace tailWord_401162 prefixEnd_401162 183101267839168609360085 := by
  unfold tailWord_401162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3657895043166515465027435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9754386781777374573406493 3657895043166515465027435)
  ·
    refine ⟨5486842564749773197541153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3657895043166515465027435 5486842564749773197541153)
    ·
      refine ⟨4115131923562329898155865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5486842564749773197541153 4115131923562329898155865)
      ·
        refine ⟨3086348942671747423616899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4115131923562329898155865 3086348942671747423616899)
        ·
          refine ⟨4629523414007621135425349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3086348942671747423616899 4629523414007621135425349)
          ·
            refine ⟨868035640126428962892253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4629523414007621135425349 868035640126428962892253)
            ·
              refine ⟨325513365047410861084595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 868035640126428962892253 325513365047410861084595)
              ·
                refine ⟨488270047571116291626893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325513365047410861084595 488270047571116291626893)
                ·
                  refine ⟨183101267839168609360085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488270047571116291626893 183101267839168609360085)
                  ·
                    rfl

theorem cell20_401162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 3].length) (baseStart_401162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401162 prefixEnd_401162 := by exact prefixLift 401162
  have htrace : WordTrace (prefixWord ++ tailWord_401162) baseStart_401162 baseEnd_401162 := by
    simpa [prefixWord, tailWord_401162, baseEnd_401162] using wordTrace_append hprefix tailTrace_401162
  have hstable : (prefixWord ++ tailWord_401162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401162).length < 2 ^ (prefixWord ++ tailWord_401162).sum := by decide
  have hdescent : baseEnd_401162 < baseStart_401162 := by decide
  rcases family_descends (prefixWord ++ tailWord_401162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401172 : List Nat := [2, 4, 4, 1, 1, 1, 1, 6]
def baseStart_401172 : Nat := 118140960795 + 401172 * 2 ^ 59
def prefixEnd_401172 : Nat := 4983230072969 + 3 ^ 40 * 401172 * 2
def baseEnd_401172 : Nat := 61035277370551006342237

theorem tailTrace_401172 : CollatzResearch.WordTrace tailWord_401172 prefixEnd_401172 61035277370551006342237 := by
  unfold tailWord_401172
  simp only [CollatzResearch.WordTrace]
  refine ⟨7315972451314916783986885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9754629935086555711982513 7315972451314916783986885)
  ·
    refine ⟨1371744834621546896997541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7315972451314916783986885 1371744834621546896997541)
    ·
      refine ⟨257202156491540043187039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1371744834621546896997541 257202156491540043187039)
      ·
        refine ⟨385803234737310064780559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257202156491540043187039 385803234737310064780559)
        ·
          refine ⟨578704852105965097170839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385803234737310064780559 578704852105965097170839)
          ·
            refine ⟨868057278158947645756259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578704852105965097170839 868057278158947645756259)
            ·
              refine ⟨1302085917238421468634389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868057278158947645756259 1302085917238421468634389)
              ·
                refine ⟨61035277370551006342237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1302085917238421468634389 61035277370551006342237)
                ·
                  rfl

theorem cell20_401172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_401172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401172 prefixEnd_401172 := by exact prefixLift 401172
  have htrace : WordTrace (prefixWord ++ tailWord_401172) baseStart_401172 baseEnd_401172 := by
    simpa [prefixWord, tailWord_401172, baseEnd_401172] using wordTrace_append hprefix tailTrace_401172
  have hstable : (prefixWord ++ tailWord_401172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401172).length < 2 ^ (prefixWord ++ tailWord_401172).sum := by decide
  have hdescent : baseEnd_401172 < baseStart_401172 := by decide
  rcases family_descends (prefixWord ++ tailWord_401172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401214 : List Nat := [4, 2, 1, 2, 2, 2, 2, 5]
def baseStart_401214 : Nat := 118140960795 + 401214 * 2 ^ 59
def prefixEnd_401214 : Nat := 4983230072969 + 3 ^ 40 * 401214 * 2
def baseEnd_401214 : Nat := 61041667352029179875513

theorem tailTrace_401214 : CollatzResearch.WordTrace tailWord_401214 prefixEnd_401214 61041667352029179875513 := by
  unfold tailWord_401214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1829184596059709342625337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9755651178985116494001797 1829184596059709342625337)
  ·
    refine ⟨1371888447044782006969003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1829184596059709342625337 1371888447044782006969003)
    ·
      refine ⟨2057832670567173010453505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1371888447044782006969003 2057832670567173010453505)
      ·
        refine ⟨1543374502925379757840129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2057832670567173010453505 1543374502925379757840129)
        ·
          refine ⟨1157530877194034818380097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1543374502925379757840129 1157530877194034818380097)
          ·
            refine ⟨868148157895526113785073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1157530877194034818380097 868148157895526113785073)
            ·
              refine ⟨651111118421644585338805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 868148157895526113785073 651111118421644585338805)
              ·
                refine ⟨61041667352029179875513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 651111118421644585338805 61041667352029179875513)
                ·
                  rfl

theorem cell20_401214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_401214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401214 prefixEnd_401214 := by exact prefixLift 401214
  have htrace : WordTrace (prefixWord ++ tailWord_401214) baseStart_401214 baseEnd_401214 := by
    simpa [prefixWord, tailWord_401214, baseEnd_401214] using wordTrace_append hprefix tailTrace_401214
  have hstable : (prefixWord ++ tailWord_401214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401214).length < 2 ^ (prefixWord ++ tailWord_401214).sum := by decide
  have hdescent : baseEnd_401214 < baseStart_401214 := by decide
  rcases family_descends (prefixWord ++ tailWord_401214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401258 : List Nat := [3, 1, 3, 4, 1, 2, 2, 2, 2]
def baseStart_401258 : Nat := 118140960795 + 401258 * 2 ^ 59
def prefixEnd_401258 : Nat := 4983230072969 + 3 ^ 40 * 401258 * 2
def baseEnd_401258 : Nat := 183145084855018942159693

theorem tailTrace_401258 : CollatzResearch.WordTrace tailWord_401258 prefixEnd_401258 183145084855018942159693 := by
  unfold tailWord_401258
  simp only [CollatzResearch.WordTrace]
  refine ⟨3658770395079567563901107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9756721053545513503736285 3658770395079567563901107)
  ·
    refine ⟨5488155592619351345851661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3658770395079567563901107 5488155592619351345851661)
    ·
      refine ⟨2058058347232256754694373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5488155592619351345851661 2058058347232256754694373)
      ·
        refine ⟨385885940106048141505195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2058058347232256754694373 385885940106048141505195)
        ·
          refine ⟨578828910159072212257793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385885940106048141505195 578828910159072212257793)
          ·
            refine ⟨434121682619304159193345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578828910159072212257793 434121682619304159193345)
            ·
              refine ⟨325591261964478119395009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434121682619304159193345 325591261964478119395009)
              ·
                refine ⟨244193446473358589546257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325591261964478119395009 244193446473358589546257)
                ·
                  refine ⟨183145084855018942159693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244193446473358589546257 183145084855018942159693)
                  ·
                    rfl

theorem cell20_401258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_401258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401258 prefixEnd_401258 := by exact prefixLift 401258
  have htrace : WordTrace (prefixWord ++ tailWord_401258) baseStart_401258 baseEnd_401258 := by
    simpa [prefixWord, tailWord_401258, baseEnd_401258] using wordTrace_append hprefix tailTrace_401258
  have hstable : (prefixWord ++ tailWord_401258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401258).length < 2 ^ (prefixWord ++ tailWord_401258).sum := by decide
  have hdescent : baseEnd_401258 < baseStart_401258 := by decide
  rcases family_descends (prefixWord ++ tailWord_401258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401262 : List Nat := [4, 1, 2, 3, 1, 2, 1, 4, 2]
def baseStart_401262 : Nat := 118140960795 + 401262 * 2 ^ 59
def prefixEnd_401262 : Nat := 4983230072969 + 3 ^ 40 * 401262 * 2
def baseEnd_401262 : Nat := 183146910564012706026343

theorem tailTrace_401262 : CollatzResearch.WordTrace tailWord_401262 prefixEnd_401262 183146910564012706026343 := by
  unfold tailWord_401262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1829403434037972367343755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9756818314869185959166693 1829403434037972367343755)
  ·
    refine ⟨2744105151056958551015633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1829403434037972367343755 2744105151056958551015633)
    ·
      refine ⟨2058078863292718913261725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2744105151056958551015633 2058078863292718913261725)
      ·
        refine ⟨771779573734769592473147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2058078863292718913261725 771779573734769592473147)
        ·
          refine ⟨1157669360602154388709721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771779573734769592473147 1157669360602154388709721)
          ·
            refine ⟨868252020451615791532291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1157669360602154388709721 868252020451615791532291)
            ·
              refine ⟨1302378030677423687298437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868252020451615791532291 1302378030677423687298437)
              ·
                refine ⟨244195880752016941368457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1302378030677423687298437 244195880752016941368457)
                ·
                  refine ⟨183146910564012706026343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244195880752016941368457 183146910564012706026343)
                  ·
                    rfl

theorem cell20_401262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_401262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401262 prefixEnd_401262 := by exact prefixLift 401262
  have htrace : WordTrace (prefixWord ++ tailWord_401262) baseStart_401262 baseEnd_401262 := by
    simpa [prefixWord, tailWord_401262, baseEnd_401262] using wordTrace_append hprefix tailTrace_401262
  have hstable : (prefixWord ++ tailWord_401262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401262).length < 2 ^ (prefixWord ++ tailWord_401262).sum := by decide
  have hdescent : baseEnd_401262 < baseStart_401262 := by decide
  rcases family_descends (prefixWord ++ tailWord_401262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401280 : List Nat := [2, 1, 1, 2, 1, 2, 3, 5, 3]
def baseStart_401280 : Nat := 118140960795 + 401280 * 2 ^ 59
def prefixEnd_401280 : Nat := 4983230072969 + 3 ^ 40 * 401280 * 2
def baseEnd_401280 : Nat := 183155126254484643426269

theorem tailTrace_401280 : CollatzResearch.WordTrace tailWord_401280 prefixEnd_401280 183155126254484643426269 := by
  unfold tailWord_401280
  simp only [CollatzResearch.WordTrace]
  refine ⟨7317941993119284006452647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9757255990825712008603529 7317941993119284006452647)
  ·
    refine ⟨10976912989678926009678971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7317941993119284006452647 10976912989678926009678971)
    ·
      refine ⟨16465369484518389014518457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10976912989678926009678971 16465369484518389014518457)
      ·
        refine ⟨12349027113388791760888843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16465369484518389014518457 12349027113388791760888843)
        ·
          refine ⟨18523540670083187641333265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12349027113388791760888843 18523540670083187641333265)
          ·
            refine ⟨13892655502562390730999949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18523540670083187641333265 13892655502562390730999949)
            ·
              refine ⟨5209745813460896524124981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13892655502562390730999949 5209745813460896524124981)
              ·
                refine ⟨488413670011959049136717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5209745813460896524124981 488413670011959049136717)
                ·
                  refine ⟨183155126254484643426269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488413670011959049136717 183155126254484643426269)
                  ·
                    rfl

theorem cell20_401280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_401280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401280 prefixEnd_401280 := by exact prefixLift 401280
  have htrace : WordTrace (prefixWord ++ tailWord_401280) baseStart_401280 baseEnd_401280 := by
    simpa [prefixWord, tailWord_401280, baseEnd_401280] using wordTrace_append hprefix tailTrace_401280
  have hstable : (prefixWord ++ tailWord_401280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401280).length < 2 ^ (prefixWord ++ tailWord_401280).sum := by decide
  have hdescent : baseEnd_401280 < baseStart_401280 := by decide
  rcases family_descends (prefixWord ++ tailWord_401280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401300 : List Nat := [2, 4, 2, 1, 1, 3, 2, 3, 2]
def baseStart_401300 : Nat := 118140960795 + 401300 * 2 ^ 59
def prefixEnd_401300 : Nat := 4983230072969 + 3 ^ 40 * 401300 * 2
def baseEnd_401300 : Nat := 183164254799453462759521

theorem tailTrace_401300 : CollatzResearch.WordTrace tailWord_401300 prefixEnd_401300 183164254799453462759521 := by
  unfold tailWord_401300
  simp only [CollatzResearch.WordTrace]
  refine ⟨7318306723083055714316677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9757742297444074285755569 7318306723083055714316677)
  ·
    refine ⟨1372182510578072946434377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7318306723083055714316677 1372182510578072946434377)
    ·
      refine ⟨1029136882933554709825783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1372182510578072946434377 1029136882933554709825783)
      ·
        refine ⟨1543705324400332064738675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029136882933554709825783 1543705324400332064738675)
        ·
          refine ⟨2315557986600498097108013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543705324400332064738675 2315557986600498097108013)
          ·
            refine ⟨868334244975186786415505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2315557986600498097108013 868334244975186786415505)
            ·
              refine ⟨651250683731390089811629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 868334244975186786415505 651250683731390089811629)
              ·
                refine ⟨244219006399271283679361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 651250683731390089811629 244219006399271283679361)
                ·
                  refine ⟨183164254799453462759521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244219006399271283679361 183164254799453462759521)
                  ·
                    rfl

theorem cell20_401300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_401300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401300 prefixEnd_401300 := by exact prefixLift 401300
  have htrace : WordTrace (prefixWord ++ tailWord_401300) baseStart_401300 baseEnd_401300 := by
    simpa [prefixWord, tailWord_401300, baseEnd_401300] using wordTrace_append hprefix tailTrace_401300
  have hstable : (prefixWord ++ tailWord_401300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401300).length < 2 ^ (prefixWord ++ tailWord_401300).sum := by decide
  have hdescent : baseEnd_401300 < baseStart_401300 := by decide
  rcases family_descends (prefixWord ++ tailWord_401300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401310 : List Nat := [4, 3, 1, 3, 1, 2, 1, 2, 3]
def baseStart_401310 : Nat := 118140960795 + 401310 * 2 ^ 59
def prefixEnd_401310 : Nat := 4983230072969 + 3 ^ 40 * 401310 * 2
def baseEnd_401310 : Nat := 183168819071937872426147

theorem tailTrace_401310 : CollatzResearch.WordTrace tailWord_401310 prefixEnd_401310 183168819071937872426147 := by
  unfold tailWord_401310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1829622272016235392062173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9757985450753255424331589 1829622272016235392062173)
  ·
    refine ⟨686108352006088272023315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1829622272016235392062173 686108352006088272023315)
    ·
      refine ⟨1029162528009132408034973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 686108352006088272023315 1029162528009132408034973)
      ·
        refine ⟨385935948003424653013115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1029162528009132408034973 385935948003424653013115)
        ·
          refine ⟨578903922005136979519673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385935948003424653013115 578903922005136979519673)
          ·
            refine ⟨434177941503852734639755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578903922005136979519673 434177941503852734639755)
            ·
              refine ⟨651266912255779101959633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434177941503852734639755 651266912255779101959633)
              ·
                refine ⟨488450184191834326469725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651266912255779101959633 488450184191834326469725)
                ·
                  refine ⟨183168819071937872426147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488450184191834326469725 183168819071937872426147)
                  ·
                    rfl

theorem cell20_401310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_401310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401310 prefixEnd_401310 := by exact prefixLift 401310
  have htrace : WordTrace (prefixWord ++ tailWord_401310) baseStart_401310 baseEnd_401310 := by
    simpa [prefixWord, tailWord_401310, baseEnd_401310] using wordTrace_append hprefix tailTrace_401310
  have hstable : (prefixWord ++ tailWord_401310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401310).length < 2 ^ (prefixWord ++ tailWord_401310).sum := by decide
  have hdescent : baseEnd_401310 < baseStart_401310 := by decide
  rcases family_descends (prefixWord ++ tailWord_401310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401311 : List Nat := [1, 1, 2, 5, 3, 1, 7]
def baseStart_401311 : Nat := 118140960795 + 401311 * 2 ^ 59
def prefixEnd_401311 : Nat := 4983230072969 + 3 ^ 40 * 401311 * 2
def baseEnd_401311 : Nat := 20352141722131812599201

theorem tailTrace_401311 : CollatzResearch.WordTrace tailWord_401311 prefixEnd_401311 20352141722131812599201 := by
  unfold tailWord_401311
  simp only [CollatzResearch.WordTrace]
  refine ⟨14637014649126260307283787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9758009766084173538189191 14637014649126260307283787)
  ·
    refine ⟨21955521973689390460925681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14637014649126260307283787 21955521973689390460925681)
    ·
      refine ⟨16466641480267042845694261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21955521973689390460925681 16466641480267042845694261)
      ·
        refine ⟨1543747638775035266783837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16466641480267042845694261 1543747638775035266783837)
        ·
          refine ⟨578905364540638225043939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1543747638775035266783837 578905364540638225043939)
          ·
            refine ⟨868358046810957337565909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578905364540638225043939 868358046810957337565909)
            ·
              refine ⟨20352141722131812599201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 868358046810957337565909 20352141722131812599201)
              ·
                rfl

theorem cell20_401311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 7].length) (baseStart_401311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401311 prefixEnd_401311 := by exact prefixLift 401311
  have htrace : WordTrace (prefixWord ++ tailWord_401311) baseStart_401311 baseEnd_401311 := by
    simpa [prefixWord, tailWord_401311, baseEnd_401311] using wordTrace_append hprefix tailTrace_401311
  have hstable : (prefixWord ++ tailWord_401311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401311).length < 2 ^ (prefixWord ++ tailWord_401311).sum := by decide
  have hdescent : baseEnd_401311 < baseStart_401311 := by decide
  rcases family_descends (prefixWord ++ tailWord_401311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401339 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 7]
def baseStart_401339 : Nat := 118140960795 + 401339 * 2 ^ 59
def prefixEnd_401339 : Nat := 4983230072969 + 3 ^ 40 * 401339 * 2
def baseEnd_401339 : Nat := 183182055462142660459361

theorem tailTrace_401339 : CollatzResearch.WordTrace tailWord_401339 prefixEnd_401339 183182055462142660459361 := by
  unfold tailWord_401339
  simp only [CollatzResearch.WordTrace]
  refine ⟨14638035893024821089303071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9758690595349880726202047 14638035893024821089303071)
  ·
    refine ⟨21957053839537231633954607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14638035893024821089303071 21957053839537231633954607)
    ·
      refine ⟨32935580759305847450931911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21957053839537231633954607 32935580759305847450931911)
      ·
        refine ⟨49403371138958771176397867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32935580759305847450931911 49403371138958771176397867)
        ·
          refine ⟨74105056708438156764596801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49403371138958771176397867 74105056708438156764596801)
          ·
            refine ⟨55578792531328617573447601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74105056708438156764596801 55578792531328617573447601)
            ·
              refine ⟨41684094398496463180085701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55578792531328617573447601 41684094398496463180085701)
              ·
                refine ⟨7815767699718086846266069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41684094398496463180085701 7815767699718086846266069)
                ·
                  refine ⟨183182055462142660459361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7815767699718086846266069 183182055462142660459361)
                  ·
                    rfl

theorem cell20_401339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_401339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401339 prefixEnd_401339 := by exact prefixLift 401339
  have htrace : WordTrace (prefixWord ++ tailWord_401339) baseStart_401339 baseEnd_401339 := by
    simpa [prefixWord, tailWord_401339, baseEnd_401339] using wordTrace_append hprefix tailTrace_401339
  have hstable : (prefixWord ++ tailWord_401339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401339).length < 2 ^ (prefixWord ++ tailWord_401339).sum := by decide
  have hdescent : baseEnd_401339 < baseStart_401339 := by decide
  rcases family_descends (prefixWord ++ tailWord_401339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401342 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_401342 : Nat := 118140960795 + 401342 * 2 ^ 59
def prefixEnd_401342 : Nat := 4983230072969 + 3 ^ 40 * 401342 * 2
def baseEnd_401342 : Nat := 183183424743887983359349

theorem tailTrace_401342 : CollatzResearch.WordTrace tailWord_401342 prefixEnd_401342 183183424743887983359349 := by
  unfold tailWord_401342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1829768164001744075207785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9758763541342635067774853 1829768164001744075207785)
  ·
    refine ⟨1372326123001308056405839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1829768164001744075207785 1372326123001308056405839)
    ·
      refine ⟨2058489184501962084608759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1372326123001308056405839 2058489184501962084608759)
      ·
        refine ⟨3087733776752943126913139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2058489184501962084608759 3087733776752943126913139)
        ·
          refine ⟨4631600665129414690369709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3087733776752943126913139 4631600665129414690369709)
          ·
            refine ⟨1736850249423530508888641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4631600665129414690369709 1736850249423530508888641)
            ·
              refine ⟨1302637687067647881666481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1736850249423530508888641 1302637687067647881666481)
              ·
                refine ⟨976978265300735911249861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302637687067647881666481 976978265300735911249861)
                ·
                  refine ⟨183183424743887983359349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 976978265300735911249861 183183424743887983359349)
                  ·
                    rfl

theorem cell20_401342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_401342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401342 prefixEnd_401342 := by exact prefixLift 401342
  have htrace : WordTrace (prefixWord ++ tailWord_401342) baseStart_401342 baseEnd_401342 := by
    simpa [prefixWord, tailWord_401342, baseEnd_401342] using wordTrace_append hprefix tailTrace_401342
  have hstable : (prefixWord ++ tailWord_401342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401342).length < 2 ^ (prefixWord ++ tailWord_401342).sum := by decide
  have hdescent : baseEnd_401342 < baseStart_401342 := by decide
  rcases family_descends (prefixWord ++ tailWord_401342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401356 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 5]
def baseStart_401356 : Nat := 118140960795 + 401356 * 2 ^ 59
def prefixEnd_401356 : Nat := 4983230072969 + 3 ^ 40 * 401356 * 2
def baseEnd_401356 : Nat := 183189814725366156892625

theorem tailTrace_401356 : CollatzResearch.WordTrace tailWord_401356 prefixEnd_401356 183189814725366156892625 := by
  unfold tailWord_401356
  simp only [CollatzResearch.WordTrace]
  refine ⟨7319327966981616496335961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9759103955975488661781281 7319327966981616496335961)
  ·
    refine ⟨5489495975236212372251971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7319327966981616496335961 5489495975236212372251971)
    ·
      refine ⟨8234243962854318558377957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5489495975236212372251971 8234243962854318558377957)
      ·
        refine ⟨1543920743035184729695867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8234243962854318558377957 1543920743035184729695867)
        ·
          refine ⟨2315881114552777094543801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543920743035184729695867 2315881114552777094543801)
          ·
            refine ⟨1736910835914582820907851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2315881114552777094543801 1736910835914582820907851)
            ·
              refine ⟨2605366253871874231361777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736910835914582820907851 2605366253871874231361777)
              ·
                refine ⟨1954024690403905673521333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2605366253871874231361777 1954024690403905673521333)
                ·
                  refine ⟨183189814725366156892625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1954024690403905673521333 183189814725366156892625)
                  ·
                    rfl

theorem cell20_401356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_401356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401356 prefixEnd_401356 := by exact prefixLift 401356
  have htrace : WordTrace (prefixWord ++ tailWord_401356) baseStart_401356 baseEnd_401356 := by
    simpa [prefixWord, tailWord_401356, baseEnd_401356] using wordTrace_append hprefix tailTrace_401356
  have hstable : (prefixWord ++ tailWord_401356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401356).length < 2 ^ (prefixWord ++ tailWord_401356).sum := by decide
  have hdescent : baseEnd_401356 < baseStart_401356 := by decide
  rcases family_descends (prefixWord ++ tailWord_401356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401372 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 4]
def baseStart_401372 : Nat := 118140960795 + 401372 * 2 ^ 59
def prefixEnd_401372 : Nat := 4983230072969 + 3 ^ 40 * 401372 * 2
def baseEnd_401372 : Nat := 183197117561341212359227

theorem tailTrace_401372 : CollatzResearch.WordTrace tailWord_401372 prefixEnd_401372 183197117561341212359227 := by
  unfold tailWord_401372
  simp only [CollatzResearch.WordTrace]
  refine ⟨7319619750952633862627185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9759493001270178483502913 7319619750952633862627185)
  ·
    refine ⟨5489714813214475396970389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7319619750952633862627185 5489714813214475396970389)
    ·
      refine ⟨257330381869428534232987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5489714813214475396970389 257330381869428534232987)
      ·
        refine ⟨385995572804142801349481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257330381869428534232987 385995572804142801349481)
        ·
          refine ⟨289496679603107101012111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385995572804142801349481 289496679603107101012111)
          ·
            refine ⟨434245019404660651518167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289496679603107101012111 434245019404660651518167)
            ·
              refine ⟨651367529106990977277251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434245019404660651518167 651367529106990977277251)
              ·
                refine ⟨977051293660486465915877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651367529106990977277251 977051293660486465915877)
                ·
                  refine ⟨183197117561341212359227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 977051293660486465915877 183197117561341212359227)
                  ·
                    rfl

theorem cell20_401372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_401372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401372 prefixEnd_401372 := by exact prefixLift 401372
  have htrace : WordTrace (prefixWord ++ tailWord_401372) baseStart_401372 baseEnd_401372 := by
    simpa [prefixWord, tailWord_401372, baseEnd_401372] using wordTrace_append hprefix tailTrace_401372
  have hstable : (prefixWord ++ tailWord_401372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401372).length < 2 ^ (prefixWord ++ tailWord_401372).sum := by decide
  have hdescent : baseEnd_401372 < baseStart_401372 := by decide
  rcases family_descends (prefixWord ++ tailWord_401372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401390 : List Nat := [4, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_401390 : Nat := 118140960795 + 401390 * 2 ^ 59
def prefixEnd_401390 : Nat := 4983230072969 + 3 ^ 40 * 401390 * 2
def baseEnd_401390 : Nat := 183205333251813149759153

theorem tailTrace_401390 : CollatzResearch.WordTrace tailWord_401390 prefixEnd_401390 183205333251813149759153 := by
  unfold tailWord_401390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1829987001980007099926203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9759930677226704532939749 1829987001980007099926203)
  ·
    refine ⟨2744980502970010649889305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1829987001980007099926203 2744980502970010649889305)
    ·
      refine ⟨2058735377227507987416979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2744980502970010649889305 2058735377227507987416979)
      ·
        refine ⟨3088103065841261981125469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2058735377227507987416979 3088103065841261981125469)
        ·
          refine ⟨1158038649690473242922051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3088103065841261981125469 1158038649690473242922051)
          ·
            refine ⟨1737057974535709864383077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158038649690473242922051 1737057974535709864383077)
            ·
              refine ⟨325698370225445599571827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1737057974535709864383077 325698370225445599571827)
              ·
                refine ⟨488547555338168399357741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325698370225445599571827 488547555338168399357741)
                ·
                  refine ⟨183205333251813149759153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488547555338168399357741 183205333251813149759153)
                  ·
                    rfl

theorem cell20_401390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_401390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401390 prefixEnd_401390 := by exact prefixLift 401390
  have htrace : WordTrace (prefixWord ++ tailWord_401390) baseStart_401390 baseEnd_401390 := by
    simpa [prefixWord, tailWord_401390, baseEnd_401390] using wordTrace_append hprefix tailTrace_401390
  have hstable : (prefixWord ++ tailWord_401390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401390).length < 2 ^ (prefixWord ++ tailWord_401390).sum := by decide
  have hdescent : baseEnd_401390 < baseStart_401390 := by decide
  rcases family_descends (prefixWord ++ tailWord_401390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401421 : List Nat := [1, 7, 1, 2, 1, 8]
def baseStart_401421 : Nat := 118140960795 + 401421 * 2 ^ 59
def prefixEnd_401421 : Nat := 4983230072969 + 3 ^ 40 * 401421 * 2
def baseEnd_401421 : Nat := 6785906759130178508359

theorem tailTrace_401421 : CollatzResearch.WordTrace tailWord_401421 prefixEnd_401421 6785906759130178508359 := by
  unfold tailWord_401421
  simp only [CollatzResearch.WordTrace]
  refine ⟨14641026678727749093788117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9760684452485166062525411 14641026678727749093788117)
  ·
    refine ⟨343149062782681619385659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 14641026678727749093788117 343149062782681619385659)
    ·
      refine ⟨514723594174022429078489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343149062782681619385659 514723594174022429078489)
      ·
        refine ⟨386042695630516821808867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514723594174022429078489 386042695630516821808867)
        ·
          refine ⟨579064043445775232713301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386042695630516821808867 579064043445775232713301)
          ·
            refine ⟨6785906759130178508359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 579064043445775232713301 6785906759130178508359)
            ·
              rfl

theorem cell20_401421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 8].length) (baseStart_401421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401421 prefixEnd_401421 := by exact prefixLift 401421
  have htrace : WordTrace (prefixWord ++ tailWord_401421) baseStart_401421 baseEnd_401421 := by
    simpa [prefixWord, tailWord_401421, baseEnd_401421] using wordTrace_append hprefix tailTrace_401421
  have hstable : (prefixWord ++ tailWord_401421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401421).length < 2 ^ (prefixWord ++ tailWord_401421).sum := by decide
  have hdescent : baseEnd_401421 < baseStart_401421 := by decide
  rcases family_descends (prefixWord ++ tailWord_401421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401431 : List Nat := [1, 1, 3, 5, 2, 2, 2, 2, 2]
def baseStart_401431 : Nat := 118140960795 + 401431 * 2 ^ 59
def prefixEnd_401431 : Nat := 4983230072969 + 3 ^ 40 * 401431 * 2
def baseEnd_401431 : Nat := 183224046768999229392319

theorem tailTrace_401431 : CollatzResearch.WordTrace tailWord_401431 prefixEnd_401431 183224046768999229392319 := by
  unfold tailWord_401431
  simp only [CollatzResearch.WordTrace]
  refine ⟨14641391408691520801652147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9760927605794347201101431 14641391408691520801652147)
  ·
    refine ⟨21962087113037281202478221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14641391408691520801652147 21962087113037281202478221)
    ·
      refine ⟨8235782667388980450929333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21962087113037281202478221 8235782667388980450929333)
      ·
        refine ⟨772104625067716917274625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8235782667388980450929333 772104625067716917274625)
        ·
          refine ⟨579078468800787687955969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 772104625067716917274625 579078468800787687955969)
          ·
            refine ⟨434308851600590765966977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 579078468800787687955969 434308851600590765966977)
            ·
              refine ⟨325731638700443074475233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434308851600590765966977 325731638700443074475233)
              ·
                refine ⟨244298729025332305856425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325731638700443074475233 244298729025332305856425)
                ·
                  refine ⟨183224046768999229392319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244298729025332305856425 183224046768999229392319)
                  ·
                    rfl

theorem cell20_401431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 2].length) (baseStart_401431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401431 prefixEnd_401431 := by exact prefixLift 401431
  have htrace : WordTrace (prefixWord ++ tailWord_401431) baseStart_401431 baseEnd_401431 := by
    simpa [prefixWord, tailWord_401431, baseEnd_401431] using wordTrace_append hprefix tailTrace_401431
  have hstable : (prefixWord ++ tailWord_401431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401431).length < 2 ^ (prefixWord ++ tailWord_401431).sum := by decide
  have hdescent : baseEnd_401431 < baseStart_401431 := by decide
  rcases family_descends (prefixWord ++ tailWord_401431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401439 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 4]
def baseStart_401439 : Nat := 118140960795 + 401439 * 2 ^ 59
def prefixEnd_401439 : Nat := 4983230072969 + 3 ^ 40 * 401439 * 2
def baseEnd_401439 : Nat := 183227698186986757125619

theorem tailTrace_401439 : CollatzResearch.WordTrace tailWord_401439 prefixEnd_401439 183227698186986757125619 := by
  unfold tailWord_401439
  simp only [CollatzResearch.WordTrace]
  refine ⟨14641683192662538167943371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9761122128441692111962247 14641683192662538167943371)
  ·
    refine ⟨21962524788993807251915057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14641683192662538167943371 21962524788993807251915057)
    ·
      refine ⟨16471893591745355438936293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21962524788993807251915057 16471893591745355438936293)
      ·
        refine ⟨3088480048452254144800555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16471893591745355438936293 3088480048452254144800555)
        ·
          refine ⟨4632720072678381217200833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3088480048452254144800555 4632720072678381217200833)
          ·
            refine ⟨3474540054508785912900625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4632720072678381217200833 3474540054508785912900625)
            ·
              refine ⟨2605905040881589434675469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3474540054508785912900625 2605905040881589434675469)
              ·
                refine ⟨977214390330596038003301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2605905040881589434675469 977214390330596038003301)
                ·
                  refine ⟨183227698186986757125619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 977214390330596038003301 183227698186986757125619)
                  ·
                    rfl

theorem cell20_401439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_401439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401439 prefixEnd_401439 := by exact prefixLift 401439
  have htrace : WordTrace (prefixWord ++ tailWord_401439) baseStart_401439 baseEnd_401439 := by
    simpa [prefixWord, tailWord_401439, baseEnd_401439] using wordTrace_append hprefix tailTrace_401439
  have hstable : (prefixWord ++ tailWord_401439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401439).length < 2 ^ (prefixWord ++ tailWord_401439).sum := by decide
  have hdescent : baseEnd_401439 < baseStart_401439 := by decide
  rcases family_descends (prefixWord ++ tailWord_401439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401473 : List Nat := [1, 2, 5, 1, 2, 1, 1, 5, 2]
def baseStart_401473 : Nat := 118140960795 + 401473 * 2 ^ 59
def prefixEnd_401473 : Nat := 4983230072969 + 3 ^ 40 * 401473 * 2
def baseEnd_401473 : Nat := 183243216713433749992147

theorem tailTrace_401473 : CollatzResearch.WordTrace tailWord_401473 prefixEnd_401473 183243216713433749992147 := by
  unfold tailWord_401473
  simp only [CollatzResearch.WordTrace]
  refine ⟨14642923274539361974681073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9761948849692907983120715 14642923274539361974681073)
  ·
    refine ⟨10982192455904521481010805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14642923274539361974681073 10982192455904521481010805)
    ·
      refine ⟨1029580542741048888844763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10982192455904521481010805 1029580542741048888844763)
      ·
        refine ⟨1544370814111573333267145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029580542741048888844763 1544370814111573333267145)
        ·
          refine ⟨1158278110583679999950359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1544370814111573333267145 1158278110583679999950359)
          ·
            refine ⟨1737417165875519999925539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158278110583679999950359 1737417165875519999925539)
            ·
              refine ⟨2606125748813279999888309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1737417165875519999925539 2606125748813279999888309)
              ·
                refine ⟨244324288951244999989529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2606125748813279999888309 244324288951244999989529)
                ·
                  refine ⟨183243216713433749992147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244324288951244999989529 183243216713433749992147)
                  ·
                    rfl

theorem cell20_401473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 2].length) (baseStart_401473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401473 prefixEnd_401473 := by exact prefixLift 401473
  have htrace : WordTrace (prefixWord ++ tailWord_401473) baseStart_401473 baseEnd_401473 := by
    simpa [prefixWord, tailWord_401473, baseEnd_401473] using wordTrace_append hprefix tailTrace_401473
  have hstable : (prefixWord ++ tailWord_401473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401473).length < 2 ^ (prefixWord ++ tailWord_401473).sum := by decide
  have hdescent : baseEnd_401473 < baseStart_401473 := by decide
  rcases family_descends (prefixWord ++ tailWord_401473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401508 : List Nat := [2, 3, 1, 1, 2, 1, 2, 5, 3]
def baseStart_401508 : Nat := 118140960795 + 401508 * 2 ^ 59
def prefixEnd_401508 : Nat := 4983230072969 + 3 ^ 40 * 401508 * 2
def baseEnd_401508 : Nat := 183259191667129183825337

theorem tailTrace_401508 : CollatzResearch.WordTrace tailWord_401508 prefixEnd_401508 183259191667129183825337 := by
  unfold tailWord_401508
  simp only [CollatzResearch.WordTrace]
  refine ⟨7322099914706281476102589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9762799886275041968136785 7322099914706281476102589)
  ·
    refine ⟨2745787468014855553538471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7322099914706281476102589 2745787468014855553538471)
    ·
      refine ⟨4118681202022283330307707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2745787468014855553538471 4118681202022283330307707)
      ·
        refine ⟨6178021803033424995461561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4118681202022283330307707 6178021803033424995461561)
        ·
          refine ⟨4633516352275068746596171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6178021803033424995461561 4633516352275068746596171)
          ·
            refine ⟨6950274528412603119894257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4633516352275068746596171 6950274528412603119894257)
            ·
              refine ⟨5212705896309452339920693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6950274528412603119894257 5212705896309452339920693)
              ·
                refine ⟨488691177779011156867565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5212705896309452339920693 488691177779011156867565)
                ·
                  refine ⟨183259191667129183825337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488691177779011156867565 183259191667129183825337)
                  ·
                    rfl

theorem cell20_401508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_401508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401508 prefixEnd_401508 := by exact prefixLift 401508
  have htrace : WordTrace (prefixWord ++ tailWord_401508) baseStart_401508 baseEnd_401508 := by
    simpa [prefixWord, tailWord_401508, baseEnd_401508] using wordTrace_append hprefix tailTrace_401508
  have hstable : (prefixWord ++ tailWord_401508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401508).length < 2 ^ (prefixWord ++ tailWord_401508).sum := by decide
  have hdescent : baseEnd_401508 < baseStart_401508 := by decide
  rcases family_descends (prefixWord ++ tailWord_401508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401546 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_401546 : Nat := 118140960795 + 401546 * 2 ^ 59
def prefixEnd_401546 : Nat := 4983230072969 + 3 ^ 40 * 401546 * 2
def baseEnd_401546 : Nat := 183276535902569940558515

theorem tailTrace_401546 : CollatzResearch.WordTrace tailWord_401546 prefixEnd_401546 183276535902569940558515 := by
  unfold tailWord_401546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661396450818723860522123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9763723868849930294725661 3661396450818723860522123)
  ·
    refine ⟨5492094676228085790783185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3661396450818723860522123 5492094676228085790783185)
    ·
      refine ⟨4119071007171064343087389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5492094676228085790783185 4119071007171064343087389)
      ·
        refine ⟨1544651627689149128657771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4119071007171064343087389 1544651627689149128657771)
        ·
          refine ⟨2316977441533723692986657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1544651627689149128657771 2316977441533723692986657)
          ·
            refine ⟨1737733081150292769739993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2316977441533723692986657 1737733081150292769739993)
            ·
              refine ⟨1303299810862719577304995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1737733081150292769739993 1303299810862719577304995)
              ·
                refine ⟨1954949716294079365957493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303299810862719577304995 1954949716294079365957493)
                ·
                  refine ⟨183276535902569940558515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1954949716294079365957493 183276535902569940558515)
                  ·
                    rfl

theorem cell20_401546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_401546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401546 prefixEnd_401546 := by exact prefixLift 401546
  have htrace : WordTrace (prefixWord ++ tailWord_401546) baseStart_401546 baseEnd_401546 := by
    simpa [prefixWord, tailWord_401546, baseEnd_401546] using wordTrace_append hprefix tailTrace_401546
  have hstable : (prefixWord ++ tailWord_401546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401546).length < 2 ^ (prefixWord ++ tailWord_401546).sum := by decide
  have hdescent : baseEnd_401546 < baseStart_401546 := by decide
  rcases family_descends (prefixWord ++ tailWord_401546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401559 : List Nat := [1, 1, 3, 3, 5, 1, 2, 1, 3]
def baseStart_401559 : Nat := 118140960795 + 401559 * 2 ^ 59
def prefixEnd_401559 : Nat := 4983230072969 + 3 ^ 40 * 401559 * 2
def baseEnd_401559 : Nat := 183282469456799673125129

theorem tailTrace_401559 : CollatzResearch.WordTrace tailWord_401559 prefixEnd_401559 183282469456799673125129 := by
  unfold tailWord_401559
  simp only [CollatzResearch.WordTrace]
  refine ⟨14646059952227798662311731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9764039968151865774874487 14646059952227798662311731)
  ·
    refine ⟨21969089928341697993467597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14646059952227798662311731 21969089928341697993467597)
    ·
      refine ⟨8238408723128136747550349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21969089928341697993467597 8238408723128136747550349)
      ·
        refine ⟨3089403271173051280331381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8238408723128136747550349 3089403271173051280331381)
        ·
          refine ⟨289631556672473557531067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3089403271173051280331381 289631556672473557531067)
          ·
            refine ⟨434447335008710336296601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289631556672473557531067 434447335008710336296601)
            ·
              refine ⟨325835501256532752222451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434447335008710336296601 325835501256532752222451)
              ·
                refine ⟨488753251884799128333677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325835501256532752222451 488753251884799128333677)
                ·
                  refine ⟨183282469456799673125129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488753251884799128333677 183282469456799673125129)
                  ·
                    rfl

theorem cell20_401559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 3].length) (baseStart_401559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401559 prefixEnd_401559 := by exact prefixLift 401559
  have htrace : WordTrace (prefixWord ++ tailWord_401559) baseStart_401559 baseEnd_401559 := by
    simpa [prefixWord, tailWord_401559, baseEnd_401559] using wordTrace_append hprefix tailTrace_401559
  have hstable : (prefixWord ++ tailWord_401559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401559).length < 2 ^ (prefixWord ++ tailWord_401559).sum := by decide
  have hdescent : baseEnd_401559 < baseStart_401559 := by decide
  rcases family_descends (prefixWord ++ tailWord_401559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401598 : List Nat := [4, 2, 1, 1, 12]
def baseStart_401598 : Nat := 118140960795 + 401598 * 2 ^ 59
def prefixEnd_401598 : Nat := 4983230072969 + 3 ^ 40 * 401598 * 2
def baseEnd_401598 : Nat := 2262966297771467541049

theorem tailTrace_401598 : CollatzResearch.WordTrace tailWord_401598 prefixEnd_401598 2262966297771467541049 := by
  unfold tailWord_401598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1830935299885813540372681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9764988266057672215320965 1830935299885813540372681)
  ·
    refine ⟨1373201474914360155279511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1830935299885813540372681 1373201474914360155279511)
    ·
      refine ⟨2059802212371540232919267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1373201474914360155279511 2059802212371540232919267)
      ·
        refine ⟨3089703318557310349378901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2059802212371540232919267 3089703318557310349378901)
        ·
          refine ⟨2262966297771467541049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3089703318557310349378901 2262966297771467541049)
          ·
            rfl

theorem cell20_401598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 12].length) (baseStart_401598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401598 prefixEnd_401598 := by exact prefixLift 401598
  have htrace : WordTrace (prefixWord ++ tailWord_401598) baseStart_401598 baseEnd_401598 := by
    simpa [prefixWord, tailWord_401598, baseEnd_401598] using wordTrace_append hprefix tailTrace_401598
  have hstable : (prefixWord ++ tailWord_401598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401598).length < 2 ^ (prefixWord ++ tailWord_401598).sum := by decide
  have hdescent : baseEnd_401598 < baseStart_401598 := by decide
  rcases family_descends (prefixWord ++ tailWord_401598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401604 : List Nat := [2, 3, 3, 1, 2, 1, 4, 2, 2]
def baseStart_401604 : Nat := 118140960795 + 401604 * 2 ^ 59
def prefixEnd_401604 : Nat := 4983230072969 + 3 ^ 40 * 401604 * 2
def baseEnd_401604 : Nat := 183303008682979516624945

theorem tailTrace_401604 : CollatzResearch.WordTrace tailWord_401604 prefixEnd_401604 183303008682979516624945 := by
  unfold tailWord_401604
  simp only [CollatzResearch.WordTrace]
  refine ⟨7323850618532385673849933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9765134158043180898466577 7323850618532385673849933)
  ·
    refine ⟨2746443981949644627693725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7323850618532385673849933 2746443981949644627693725)
    ·
      refine ⟨1029916493231116735385147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2746443981949644627693725 1029916493231116735385147)
      ·
        refine ⟨1544874739846675103077721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029916493231116735385147 1544874739846675103077721)
        ·
          refine ⟨1158656054885006327308291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1544874739846675103077721 1158656054885006327308291)
          ·
            refine ⟨1737984082327509490962437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158656054885006327308291 1737984082327509490962437)
            ·
              refine ⟨325872015436408029555457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1737984082327509490962437 325872015436408029555457)
              ·
                refine ⟨244404011577306022166593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325872015436408029555457 244404011577306022166593)
                ·
                  refine ⟨183303008682979516624945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 244404011577306022166593 183303008682979516624945)
                  ·
                    rfl

theorem cell20_401604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_401604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401604 prefixEnd_401604 := by exact prefixLift 401604
  have htrace : WordTrace (prefixWord ++ tailWord_401604) baseStart_401604 baseEnd_401604 := by
    simpa [prefixWord, tailWord_401604, baseEnd_401604] using wordTrace_append hprefix tailTrace_401604
  have hstable : (prefixWord ++ tailWord_401604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401604).length < 2 ^ (prefixWord ++ tailWord_401604).sum := by decide
  have hdescent : baseEnd_401604 < baseStart_401604 := by decide
  rcases family_descends (prefixWord ++ tailWord_401604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401605 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 5]
def baseStart_401605 : Nat := 118140960795 + 401605 * 2 ^ 59
def prefixEnd_401605 : Nat := 4983230072969 + 3 ^ 40 * 401605 * 2
def baseEnd_401605 : Nat := 183303465110227957591607

theorem tailTrace_401605 : CollatzResearch.WordTrace tailWord_401605 prefixEnd_401605 183303465110227957591607 := by
  unfold tailWord_401605
  simp only [CollatzResearch.WordTrace]
  refine ⟨14647737710061148518486269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9765158473374099012324179 14647737710061148518486269)
  ·
    refine ⟨5492901641272930694432351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14647737710061148518486269 5492901641272930694432351)
    ·
      refine ⟨8239352461909396041648527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5492901641272930694432351 8239352461909396041648527)
      ·
        refine ⟨12359028692864094062472791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8239352461909396041648527 12359028692864094062472791)
        ·
          refine ⟨18538543039296141093709187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12359028692864094062472791 18538543039296141093709187)
          ·
            refine ⟨27807814558944211640563781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18538543039296141093709187 27807814558944211640563781)
            ·
              refine ⟨5213965229802039682605709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27807814558944211640563781 5213965229802039682605709)
              ·
                refine ⟨1955236961175764880977141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5213965229802039682605709 1955236961175764880977141)
                ·
                  refine ⟨183303465110227957591607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1955236961175764880977141 183303465110227957591607)
                  ·
                    rfl

theorem cell20_401605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_401605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401605 prefixEnd_401605 := by exact prefixLift 401605
  have htrace : WordTrace (prefixWord ++ tailWord_401605) baseStart_401605 baseEnd_401605 := by
    simpa [prefixWord, tailWord_401605, baseEnd_401605] using wordTrace_append hprefix tailTrace_401605
  have hstable : (prefixWord ++ tailWord_401605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401605).length < 2 ^ (prefixWord ++ tailWord_401605).sum := by decide
  have hdescent : baseEnd_401605 < baseStart_401605 := by decide
  rcases family_descends (prefixWord ++ tailWord_401605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401643 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 5]
def baseStart_401643 : Nat := 118140960795 + 401643 * 2 ^ 59
def prefixEnd_401643 : Nat := 4983230072969 + 3 ^ 40 * 401643 * 2
def baseEnd_401643 : Nat := 183320809345668714324785

theorem tailTrace_401643 : CollatzResearch.WordTrace tailWord_401643 prefixEnd_401643 183320809345668714324785 := by
  unfold tailWord_401643
  simp only [CollatzResearch.WordTrace]
  refine ⟨14649123683923481008369583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9766082455948987338913055 14649123683923481008369583)
  ·
    refine ⟨21973685525885221512554375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14649123683923481008369583 21973685525885221512554375)
    ·
      refine ⟨32960528288827832268831563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21973685525885221512554375 32960528288827832268831563)
      ·
        refine ⟨49440792433241748403247345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32960528288827832268831563 49440792433241748403247345)
        ·
          refine ⟨37080594324931311302435509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49440792433241748403247345 37080594324931311302435509)
          ·
            refine ⟨3476305717962310434603329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37080594324931311302435509 3476305717962310434603329)
            ·
              refine ⟨2607229288471732825952497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3476305717962310434603329 2607229288471732825952497)
              ·
                refine ⟨1955421966353799619464373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2607229288471732825952497 1955421966353799619464373)
                ·
                  refine ⟨183320809345668714324785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1955421966353799619464373 183320809345668714324785)
                  ·
                    rfl

theorem cell20_401643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_401643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401643 prefixEnd_401643 := by exact prefixLift 401643
  have htrace : WordTrace (prefixWord ++ tailWord_401643) baseStart_401643 baseEnd_401643 := by
    simpa [prefixWord, tailWord_401643, baseEnd_401643] using wordTrace_append hprefix tailTrace_401643
  have hstable : (prefixWord ++ tailWord_401643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401643).length < 2 ^ (prefixWord ++ tailWord_401643).sum := by decide
  have hdescent : baseEnd_401643 < baseStart_401643 := by decide
  rcases family_descends (prefixWord ++ tailWord_401643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401660 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 5]
def baseStart_401660 : Nat := 118140960795 + 401660 * 2 ^ 59
def prefixEnd_401660 : Nat := 4983230072969 + 3 ^ 40 * 401660 * 2
def baseEnd_401660 : Nat := 183328568608892210758049

theorem tailTrace_401660 : CollatzResearch.WordTrace tailWord_401660 prefixEnd_401660 183328568608892210758049 := by
  unfold tailWord_401660
  simp only [CollatzResearch.WordTrace]
  refine ⟨7324871862430946455869217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9766495816574595274492289 7324871862430946455869217)
  ·
    refine ⟨5493653896823209841901913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7324871862430946455869217 5493653896823209841901913)
    ·
      refine ⟨4120240422617407381426435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5493653896823209841901913 4120240422617407381426435)
      ·
        refine ⟨6180360633926111072139653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4120240422617407381426435 6180360633926111072139653)
        ·
          refine ⟨1158817618861145826026185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6180360633926111072139653 1158817618861145826026185)
          ·
            refine ⟨869113214145859369519639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1158817618861145826026185 869113214145859369519639)
            ·
              refine ⟨1303669821218789054279459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869113214145859369519639 1303669821218789054279459)
              ·
                refine ⟨1955504731828183581419189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303669821218789054279459 1955504731828183581419189)
                ·
                  refine ⟨183328568608892210758049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1955504731828183581419189 183328568608892210758049)
                  ·
                    rfl

theorem cell20_401660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_401660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401660 prefixEnd_401660 := by exact prefixLift 401660
  have htrace : WordTrace (prefixWord ++ tailWord_401660) baseStart_401660 baseEnd_401660 := by
    simpa [prefixWord, tailWord_401660, baseEnd_401660] using wordTrace_append hprefix tailTrace_401660
  have hstable : (prefixWord ++ tailWord_401660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401660).length < 2 ^ (prefixWord ++ tailWord_401660).sum := by decide
  have hdescent : baseEnd_401660 < baseStart_401660 := by decide
  rcases family_descends (prefixWord ++ tailWord_401660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401667 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 4]
def baseStart_401667 : Nat := 118140960795 + 401667 * 2 ^ 59
def prefixEnd_401667 : Nat := 4983230072969 + 3 ^ 40 * 401667 * 2
def baseEnd_401667 : Nat := 183331763599631297524687

theorem tailTrace_401667 : CollatzResearch.WordTrace tailWord_401667 prefixEnd_401667 183331763599631297524687 := by
  unfold tailWord_401667
  simp only [CollatzResearch.WordTrace]
  refine ⟨14649999035836533107243255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9766666023891022071495503 14649999035836533107243255)
  ·
    refine ⟨21974998553754799660864883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14649999035836533107243255 21974998553754799660864883)
    ·
      refine ⟨32962497830632199491297325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21974998553754799660864883 32962497830632199491297325)
      ·
        refine ⟨12360936686487074809236497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32962497830632199491297325 12360936686487074809236497)
        ·
          refine ⟨9270702514865306106927373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12360936686487074809236497 9270702514865306106927373)
          ·
            refine ⟨3476513443074489790097765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9270702514865306106927373 3476513443074489790097765)
            ·
              refine ⟨651846270576466835643331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3476513443074489790097765 651846270576466835643331)
              ·
                refine ⟨977769405864700253464997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651846270576466835643331 977769405864700253464997)
                ·
                  refine ⟨183331763599631297524687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 977769405864700253464997 183331763599631297524687)
                  ·
                    rfl

theorem cell20_401667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 4].length) (baseStart_401667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401667 prefixEnd_401667 := by exact prefixLift 401667
  have htrace : WordTrace (prefixWord ++ tailWord_401667) baseStart_401667 baseEnd_401667 := by
    simpa [prefixWord, tailWord_401667, baseEnd_401667] using wordTrace_append hprefix tailTrace_401667
  have hstable : (prefixWord ++ tailWord_401667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401667).length < 2 ^ (prefixWord ++ tailWord_401667).sum := by decide
  have hdescent : baseEnd_401667 < baseStart_401667 := by decide
  rcases family_descends (prefixWord ++ tailWord_401667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401698 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_401698 : Nat := 118140960795 + 401698 * 2 ^ 59
def prefixEnd_401698 : Nat := 4983230072969 + 3 ^ 40 * 401698 * 2
def baseEnd_401698 : Nat := 183345912844332967491227

theorem tailTrace_401698 : CollatzResearch.WordTrace tailWord_401698 prefixEnd_401698 183345912844332967491227 := by
  unfold tailWord_401698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3662782424681056350405437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9767419799149483601081165 3662782424681056350405437)
  ·
    refine ⟨1373543409255396131402039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3662782424681056350405437 1373543409255396131402039)
    ·
      refine ⟨2060315113883094197103059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1373543409255396131402039 2060315113883094197103059)
      ·
        refine ⟨3090472670824641295654589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2060315113883094197103059 3090472670824641295654589)
        ·
          refine ⟨1158927251559240485870471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3090472670824641295654589 1158927251559240485870471)
          ·
            refine ⟨1738390877338860728805707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158927251559240485870471 1738390877338860728805707)
            ·
              refine ⟨2607586316008291093208561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738390877338860728805707 2607586316008291093208561)
              ·
                refine ⟨1955689737006218319906421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2607586316008291093208561 1955689737006218319906421)
                ·
                  refine ⟨183345912844332967491227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1955689737006218319906421 183345912844332967491227)
                  ·
                    rfl

theorem cell20_401698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_401698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401698 prefixEnd_401698 := by exact prefixLift 401698
  have htrace : WordTrace (prefixWord ++ tailWord_401698) baseStart_401698 baseEnd_401698 := by
    simpa [prefixWord, tailWord_401698, baseEnd_401698] using wordTrace_append hprefix tailTrace_401698
  have hstable : (prefixWord ++ tailWord_401698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401698).length < 2 ^ (prefixWord ++ tailWord_401698).sum := by decide
  have hdescent : baseEnd_401698 < baseStart_401698 := by decide
  rcases family_descends (prefixWord ++ tailWord_401698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401722 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 4]
def baseStart_401722 : Nat := 118140960795 + 401722 * 2 ^ 59
def prefixEnd_401722 : Nat := 4983230072969 + 3 ^ 40 * 401722 * 2
def baseEnd_401722 : Nat := 183356867098295550691129

theorem tailTrace_401722 : CollatzResearch.WordTrace tailWord_401722 prefixEnd_401722 183356867098295550691129 := by
  unfold tailWord_401722
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663001262659319375123855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9768003367091518333663613 3663001262659319375123855)
  ·
    refine ⟨5494501893988979062685783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3663001262659319375123855 5494501893988979062685783)
    ·
      refine ⟨8241752840983468594028675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5494501893988979062685783 8241752840983468594028675)
      ·
        refine ⟨12362629261475202891043013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8241752840983468594028675 12362629261475202891043013)
        ·
          refine ⟨2317992986526600542070565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12362629261475202891043013 2317992986526600542070565)
          ·
            refine ⟨434623684973737601638231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2317992986526600542070565 434623684973737601638231)
            ·
              refine ⟨651935527460606402457347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434623684973737601638231 651935527460606402457347)
              ·
                refine ⟨977903291190909603686021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651935527460606402457347 977903291190909603686021)
                ·
                  refine ⟨183356867098295550691129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 977903291190909603686021 183356867098295550691129)
                  ·
                    rfl

theorem cell20_401722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_401722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401722 prefixEnd_401722 := by exact prefixLift 401722
  have htrace : WordTrace (prefixWord ++ tailWord_401722) baseStart_401722 baseEnd_401722 := by
    simpa [prefixWord, tailWord_401722, baseEnd_401722] using wordTrace_append hprefix tailTrace_401722
  have hstable : (prefixWord ++ tailWord_401722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401722).length < 2 ^ (prefixWord ++ tailWord_401722).sum := by decide
  have hdescent : baseEnd_401722 < baseStart_401722 := by decide
  rcases family_descends (prefixWord ++ tailWord_401722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401732 : List Nat := [2, 3, 4, 1, 2, 1, 1, 3, 3]
def baseStart_401732 : Nat := 118140960795 + 401732 * 2 ^ 59
def prefixEnd_401732 : Nat := 4983230072969 + 3 ^ 40 * 401732 * 2
def baseEnd_401732 : Nat := 183361431370779960357755

theorem tailTrace_401732 : CollatzResearch.WordTrace tailWord_401732 prefixEnd_401732 183361431370779960357755 := by
  unfold tailWord_401732
  simp only [CollatzResearch.WordTrace]
  refine ⟨7326184890300524604179725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9768246520400699472239633 7326184890300524604179725)
  ·
    refine ⟨2747319333862696726567397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7326184890300524604179725 2747319333862696726567397)
    ·
      refine ⟨515122375099255636231387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2747319333862696726567397 515122375099255636231387)
      ·
        refine ⟨772683562648883454347081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515122375099255636231387 772683562648883454347081)
        ·
          refine ⟨579512671986662590760311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 772683562648883454347081 579512671986662590760311)
          ·
            refine ⟨869269007979993886140467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579512671986662590760311 869269007979993886140467)
            ·
              refine ⟨1303903511969990829210701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869269007979993886140467 1303903511969990829210701)
              ·
                refine ⟨488963816988746560954013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1303903511969990829210701 488963816988746560954013)
                ·
                  refine ⟨183361431370779960357755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 488963816988746560954013 183361431370779960357755)
                  ·
                    rfl

theorem cell20_401732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_401732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401732 prefixEnd_401732 := by exact prefixLift 401732
  have htrace : WordTrace (prefixWord ++ tailWord_401732) baseStart_401732 baseEnd_401732 := by
    simpa [prefixWord, tailWord_401732, baseEnd_401732] using wordTrace_append hprefix tailTrace_401732
  have hstable : (prefixWord ++ tailWord_401732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401732).length < 2 ^ (prefixWord ++ tailWord_401732).sum := by decide
  have hdescent : baseEnd_401732 < baseStart_401732 := by decide
  rcases family_descends (prefixWord ++ tailWord_401732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401825 : List Nat := [1, 2, 3, 5, 2, 1, 1, 2, 3]
def baseStart_401825 : Nat := 118140960795 + 401825 * 2 ^ 59
def prefixEnd_401825 : Nat := 4983230072969 + 3 ^ 40 * 401825 * 2
def baseEnd_401825 : Nat := 183403879104884970257375

theorem tailTrace_401825 : CollatzResearch.WordTrace tailWord_401825 prefixEnd_401825 183403879104884970257375 := by
  unfold tailWord_401825
  simp only [CollatzResearch.WordTrace]
  refine ⟨14655761769264126091494929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9770507846176084060996619 14655761769264126091494929)
  ·
    refine ⟨10991821326948094568621197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14655761769264126091494929 10991821326948094568621197)
    ·
      refine ⟨4121932997605535463232949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10991821326948094568621197 4121932997605535463232949)
      ·
        refine ⟨386431218525518949678089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4121932997605535463232949 386431218525518949678089)
        ·
          refine ⟨289823413894139212258567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386431218525518949678089 289823413894139212258567)
          ·
            refine ⟨434735120841208818387851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289823413894139212258567 434735120841208818387851)
            ·
              refine ⟨652102681261813227581777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434735120841208818387851 652102681261813227581777)
              ·
                refine ⟨489077010946359920686333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 652102681261813227581777 489077010946359920686333)
                ·
                  refine ⟨183403879104884970257375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 489077010946359920686333 183403879104884970257375)
                  ·
                    rfl

theorem cell20_401825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 3].length) (baseStart_401825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_401825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_401825 prefixEnd_401825 := by exact prefixLift 401825
  have htrace : WordTrace (prefixWord ++ tailWord_401825) baseStart_401825 baseEnd_401825 := by
    simpa [prefixWord, tailWord_401825, baseEnd_401825] using wordTrace_append hprefix tailTrace_401825
  have hstable : (prefixWord ++ tailWord_401825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401825).length < 2 ^ (prefixWord ++ tailWord_401825).sum := by decide
  have hdescent : baseEnd_401825 < baseStart_401825 := by decide
  rcases family_descends (prefixWord ++ tailWord_401825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
