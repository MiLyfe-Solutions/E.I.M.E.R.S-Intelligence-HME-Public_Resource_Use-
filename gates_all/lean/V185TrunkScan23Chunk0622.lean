import V185TrunkScan23Chunk0621

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3678189 : List Nat := [1, 5, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_3678189 : Nat := 118140960795 + 3678189 * 2 ^ 59
def prefixEnd_3678189 : Nat := 4983230072969 + 3 ^ 40 * 3678189 * 2
def baseEnd_3678189 : Nat := 629559631693471600773941

theorem tailTrace_3678189 : CollatzResearch.WordTrace tailWord_3678189 prefixEnd_3678189 629559631693471600773941 := by
  unfold tailWord_3678189
  simp only [CollatzResearch.WordTrace]
  refine ⟨134154574071556912513973621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89436382714371275009315747 134154574071556912513973621)
  ·
    refine ⟨12576991319208460548185027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134154574071556912513973621 12576991319208460548185027)
    ·
      refine ⟨18865486978812690822277541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12576991319208460548185027 18865486978812690822277541)
      ·
        refine ⟨3537278808527379529177039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18865486978812690822277541 3537278808527379529177039)
        ·
          refine ⟨5305918212791069293765559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3537278808527379529177039 5305918212791069293765559)
          ·
            refine ⟨7958877319186603940648339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5305918212791069293765559 7958877319186603940648339)
            ·
              refine ⟨11938315978779905910972509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7958877319186603940648339 11938315978779905910972509)
              ·
                refine ⟨4476868492042464716614691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11938315978779905910972509 4476868492042464716614691)
                ·
                  refine ⟨6715302738063697074922037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476868492042464716614691 6715302738063697074922037)
                  ·
                    refine ⟨629559631693471600773941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6715302738063697074922037 629559631693471600773941)
                    ·
                      rfl

theorem cell23_3678189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_3678189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678189 prefixEnd_3678189 := by exact prefixLift 3678189
  have htrace : WordTrace (prefixWord ++ tailWord_3678189) baseStart_3678189 baseEnd_3678189 := by
    simpa [prefixWord, tailWord_3678189, baseEnd_3678189] using wordTrace_append hprefix tailTrace_3678189
  have hstable : (prefixWord ++ tailWord_3678189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678189).length < 2 ^ (prefixWord ++ tailWord_3678189).sum := by decide
  have hdescent : baseEnd_3678189 < baseStart_3678189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678192 : List Nat := [2, 1, 1, 1, 3, 2, 6, 1, 1, 1, 4]
def baseStart_3678192 : Nat := 118140960795 + 3678192 * 2 ^ 59
def prefixEnd_3678192 : Nat := 4983230072969 + 3 ^ 40 * 3678192 * 2
def baseEnd_3678192 : Nat := 1888680435522378290584309

theorem tailTrace_3678192 : CollatzResearch.WordTrace tailWord_3678192 prefixEnd_3678192 1888680435522378290584309 := by
  unfold tailWord_3678192
  simp only [CollatzResearch.WordTrace]
  refine ⟨67077341745273022013166415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89436455660364029350888553 67077341745273022013166415)
  ·
    refine ⟨100616012617909533019749623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67077341745273022013166415 100616012617909533019749623)
    ·
      refine ⟨150924018926864299529624435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100616012617909533019749623 150924018926864299529624435)
      ·
        refine ⟨226386028390296449294436653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150924018926864299529624435 226386028390296449294436653)
        ·
          refine ⟨84894760646361168485413745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226386028390296449294436653 84894760646361168485413745)
          ·
            refine ⟨63671070484770876364060309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84894760646361168485413745 63671070484770876364060309)
            ·
              refine ⟨2984581428973634829565327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63671070484770876364060309 2984581428973634829565327)
              ·
                refine ⟨4476872143460452244347991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984581428973634829565327 4476872143460452244347991)
                ·
                  refine ⟨6715308215190678366521987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476872143460452244347991 6715308215190678366521987)
                  ·
                    refine ⟨10072962322786017549782981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6715308215190678366521987 10072962322786017549782981)
                    ·
                      refine ⟨1888680435522378290584309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10072962322786017549782981 1888680435522378290584309)
                      ·
                        rfl

theorem cell23_3678192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 1, 1, 4].length) (baseStart_3678192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678192 prefixEnd_3678192 := by exact prefixLift 3678192
  have htrace : WordTrace (prefixWord ++ tailWord_3678192) baseStart_3678192 baseEnd_3678192 := by
    simpa [prefixWord, tailWord_3678192, baseEnd_3678192] using wordTrace_append hprefix tailTrace_3678192
  have hstable : (prefixWord ++ tailWord_3678192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678192).length < 2 ^ (prefixWord ++ tailWord_3678192).sum := by decide
  have hdescent : baseEnd_3678192 < baseStart_3678192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678209 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 3, 2, 2]
def baseStart_3678209 : Nat := 118140960795 + 3678209 * 2 ^ 59
def prefixEnd_3678209 : Nat := 4983230072969 + 3 ^ 40 * 3678209 * 2
def baseEnd_3678209 : Nat := 1888689164693504724071731

theorem tailTrace_3678209 : CollatzResearch.WordTrace tailWord_3678209 prefixEnd_3678209 1888689164693504724071731 := by
  unfold tailWord_3678209
  simp only [CollatzResearch.WordTrace]
  refine ⟨134155303531484455929701681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89436869020989637286467787 134155303531484455929701681)
  ·
    refine ⟨100616477648613341947276261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134155303531484455929701681 100616477648613341947276261)
    ·
      refine ⟨18865589559115001615114299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100616477648613341947276261 18865589559115001615114299)
      ·
        refine ⟨28298384338672502422671449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18865589559115001615114299 28298384338672502422671449)
        ·
          refine ⟨21223788254004376817003587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28298384338672502422671449 21223788254004376817003587)
          ·
            refine ⟨31835682381006565225505381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21223788254004376817003587 31835682381006565225505381)
            ·
              refine ⟨5969190446438730979782259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31835682381006565225505381 5969190446438730979782259)
              ·
                refine ⟨8953785669658096469673389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5969190446438730979782259 8953785669658096469673389)
                ·
                  refine ⟨3357669626121786176127521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8953785669658096469673389 3357669626121786176127521)
                  ·
                    refine ⟨2518252219591339632095641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3357669626121786176127521 2518252219591339632095641)
                    ·
                      refine ⟨1888689164693504724071731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518252219591339632095641 1888689164693504724071731)
                      ·
                        rfl

theorem cell23_3678209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_3678209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678209 prefixEnd_3678209 := by exact prefixLift 3678209
  have htrace : WordTrace (prefixWord ++ tailWord_3678209) baseStart_3678209 baseEnd_3678209 := by
    simpa [prefixWord, tailWord_3678209, baseEnd_3678209] using wordTrace_append hprefix tailTrace_3678209
  have hstable : (prefixWord ++ tailWord_3678209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678209).length < 2 ^ (prefixWord ++ tailWord_3678209).sum := by decide
  have hdescent : baseEnd_3678209 < baseStart_3678209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678229 : List Nat := [1, 3, 2, 1, 5, 1, 2, 2, 1, 2, 3]
def baseStart_3678229 : Nat := 118140960795 + 3678229 * 2 ^ 59
def prefixEnd_3678229 : Nat := 4983230072969 + 3 ^ 40 * 3678229 * 2
def baseEnd_3678229 : Nat := 1888699434306594645821639

theorem tailTrace_3678229 : CollatzResearch.WordTrace tailWord_3678229 prefixEnd_3678229 1888699434306594645821639 := by
  unfold tailWord_3678229
  simp only [CollatzResearch.WordTrace]
  refine ⟨134156032991411999345429741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89437355327607999563619827 134156032991411999345429741)
  ·
    refine ⟨50308512371779499754536153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134156032991411999345429741 50308512371779499754536153)
    ·
      refine ⟨37731384278834624815902115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50308512371779499754536153 37731384278834624815902115)
      ·
        refine ⟨56597076418251937223853173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37731384278834624815902115 56597076418251937223853173)
        ·
          refine ⟨5305975914211119114736235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56597076418251937223853173 5305975914211119114736235)
          ·
            refine ⟨7958963871316678672104353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5305975914211119114736235 7958963871316678672104353)
            ·
              refine ⟨5969222903487509004078265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7958963871316678672104353 5969222903487509004078265)
              ·
                refine ⟨4476917177615631753058699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5969222903487509004078265 4476917177615631753058699)
                ·
                  refine ⟨6715375766423447629588049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476917177615631753058699 6715375766423447629588049)
                  ·
                    refine ⟨5036531824817585722191037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6715375766423447629588049 5036531824817585722191037)
                    ·
                      refine ⟨1888699434306594645821639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5036531824817585722191037 1888699434306594645821639)
                      ·
                        rfl

theorem cell23_3678229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_3678229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678229 prefixEnd_3678229 := by exact prefixLift 3678229
  have htrace : WordTrace (prefixWord ++ tailWord_3678229) baseStart_3678229 baseEnd_3678229 := by
    simpa [prefixWord, tailWord_3678229, baseEnd_3678229] using wordTrace_append hprefix tailTrace_3678229
  have hstable : (prefixWord ++ tailWord_3678229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678229).length < 2 ^ (prefixWord ++ tailWord_3678229).sum := by decide
  have hdescent : baseEnd_3678229 < baseStart_3678229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678242 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_3678242 : Nat := 118140960795 + 3678242 * 2 ^ 59
def prefixEnd_3678242 : Nat := 4983230072969 + 3 ^ 40 * 3678242 * 2
def baseEnd_3678242 : Nat := 1888706109555103094959079

theorem tailTrace_3678242 : CollatzResearch.WordTrace tailWord_3678242 prefixEnd_3678242 1888706109555103094959079 := by
  unfold tailWord_3678242
  simp only [CollatzResearch.WordTrace]
  refine ⟨33539126785091225641413245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89437671426909935043768653 33539126785091225641413245)
  ·
    refine ⟨12577172544409209615529967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33539126785091225641413245 12577172544409209615529967)
    ·
      refine ⟨18865758816613814423294951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12577172544409209615529967 18865758816613814423294951)
      ·
        refine ⟨28298638224920721634942427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18865758816613814423294951 28298638224920721634942427)
        ·
          refine ⟨42447957337381082452413641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28298638224920721634942427 42447957337381082452413641)
          ·
            refine ⟨31835968003035811839310231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42447957337381082452413641 31835968003035811839310231)
            ·
              refine ⟨47753952004553717758965347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31835968003035811839310231 47753952004553717758965347)
              ·
                refine ⟨71630928006830576638448021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47753952004553717758965347 71630928006830576638448021)
                ·
                  refine ⟨3357699750320183279927251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71630928006830576638448021 3357699750320183279927251)
                  ·
                    refine ⟨5036549625480274919890877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3357699750320183279927251 5036549625480274919890877)
                    ·
                      refine ⟨1888706109555103094959079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5036549625480274919890877 1888706109555103094959079)
                      ·
                        rfl

theorem cell23_3678242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_3678242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678242 prefixEnd_3678242 := by exact prefixLift 3678242
  have htrace : WordTrace (prefixWord ++ tailWord_3678242) baseStart_3678242 baseEnd_3678242 := by
    simpa [prefixWord, tailWord_3678242, baseEnd_3678242] using wordTrace_append hprefix tailTrace_3678242
  have hstable : (prefixWord ++ tailWord_3678242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678242).length < 2 ^ (prefixWord ++ tailWord_3678242).sum := by decide
  have hdescent : baseEnd_3678242 < baseStart_3678242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678260 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_3678260 : Nat := 118140960795 + 3678260 * 2 ^ 59
def prefixEnd_3678260 : Nat := 4983230072969 + 3 ^ 40 * 3678260 * 2
def baseEnd_3678260 : Nat := 1888715352206884024533997

theorem tailTrace_3678260 : CollatzResearch.WordTrace tailWord_3678260 prefixEnd_3678260 1888715352206884024533997 := by
  unfold tailWord_3678260
  simp only [CollatzResearch.WordTrace]
  refine ⟨67078581827149845819904117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89438109102866461093205489 67078581827149845819904117)
  ·
    refine ⟨6288617046295298045616011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67078581827149845819904117 6288617046295298045616011)
    ·
      refine ⟨9432925569442947068424017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6288617046295298045616011 9432925569442947068424017)
      ·
        refine ⟨7074694177082210301318013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9432925569442947068424017 7074694177082210301318013)
        ·
          refine ⟨2653010316405828862994255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7074694177082210301318013 2653010316405828862994255)
          ·
            refine ⟨3979515474608743294491383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2653010316405828862994255 3979515474608743294491383)
            ·
              refine ⟨5969273211913114941737075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3979515474608743294491383 5969273211913114941737075)
              ·
                refine ⟨8953909817869672412605613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5969273211913114941737075 8953909817869672412605613)
                ·
                  refine ⟨3357716181701127154727105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8953909817869672412605613 3357716181701127154727105)
                  ·
                    refine ⟨2518287136275845366045329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3357716181701127154727105 2518287136275845366045329)
                    ·
                      refine ⟨1888715352206884024533997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518287136275845366045329 1888715352206884024533997)
                      ·
                        rfl

theorem cell23_3678260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_3678260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678260 prefixEnd_3678260 := by exact prefixLift 3678260
  have htrace : WordTrace (prefixWord ++ tailWord_3678260) baseStart_3678260 baseEnd_3678260 := by
    simpa [prefixWord, tailWord_3678260, baseEnd_3678260] using wordTrace_append hprefix tailTrace_3678260
  have hstable : (prefixWord ++ tailWord_3678260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678260).length < 2 ^ (prefixWord ++ tailWord_3678260).sum := by decide
  have hdescent : baseEnd_3678260 < baseStart_3678260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678282 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 1, 4, 2]
def baseStart_3678282 : Nat := 118140960795 + 3678282 * 2 ^ 59
def prefixEnd_3678282 : Nat := 4983230072969 + 3 ^ 40 * 3678282 * 2
def baseEnd_3678282 : Nat := 1888726648781282938458895

theorem tailTrace_3678282 : CollatzResearch.WordTrace tailWord_3678282 prefixEnd_3678282 1888726648781282938458895 := by
  unfold tailWord_3678282
  simp only [CollatzResearch.WordTrace]
  refine ⟨33539491515054997349277275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89438644040146659598072733 33539491515054997349277275)
  ·
    refine ⟨50309237272582496023915913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33539491515054997349277275 50309237272582496023915913)
    ·
      refine ⟨37731927954436872017936935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50309237272582496023915913 37731927954436872017936935)
      ·
        refine ⟨56597891931655308026905403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37731927954436872017936935 56597891931655308026905403)
        ·
          refine ⟨84896837897482962040358105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56597891931655308026905403 84896837897482962040358105)
          ·
            refine ⟨63672628423112221530268579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84896837897482962040358105 63672628423112221530268579)
            ·
              refine ⟨95508942634668332295402869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63672628423112221530268579 95508942634668332295402869)
              ·
                refine ⟨8953963372000156152694019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95508942634668332295402869 8953963372000156152694019)
                ·
                  refine ⟨13430945058000234229041029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8953963372000156152694019 13430945058000234229041029)
                  ·
                    refine ⟨2518302198375043917945193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13430945058000234229041029 2518302198375043917945193)
                    ·
                      refine ⟨1888726648781282938458895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518302198375043917945193 1888726648781282938458895)
                      ·
                        rfl

theorem cell23_3678282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_3678282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678282 prefixEnd_3678282 := by exact prefixLift 3678282
  have htrace : WordTrace (prefixWord ++ tailWord_3678282) baseStart_3678282 baseEnd_3678282 := by
    simpa [prefixWord, tailWord_3678282, baseEnd_3678282] using wordTrace_append hprefix tailTrace_3678282
  have hstable : (prefixWord ++ tailWord_3678282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678282).length < 2 ^ (prefixWord ++ tailWord_3678282).sum := by decide
  have hdescent : baseEnd_3678282 < baseStart_3678282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678286 : List Nat := [4, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2]
def baseStart_3678286 : Nat := 118140960795 + 3678286 * 2 ^ 59
def prefixEnd_3678286 : Nat := 4983230072969 + 3 ^ 40 * 3678286 * 2
def baseEnd_3678286 : Nat := 1888728702703900922808877

theorem tailTrace_3678286 : CollatzResearch.WordTrace tailWord_3678286 prefixEnd_3678286 1888728702703900922808877 := by
  unfold tailWord_3678286
  simp only [CollatzResearch.WordTrace]
  refine ⟨16769763994025687260031839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89438741301470332053503141 16769763994025687260031839)
  ·
    refine ⟨25154645991038530890047759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16769763994025687260031839 25154645991038530890047759)
    ·
      refine ⟨37731968986557796335071639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25154645991038530890047759 37731968986557796335071639)
      ·
        refine ⟨56597953479836694502607459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37731968986557796335071639 56597953479836694502607459)
        ·
          refine ⟨84896930219755041753911189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56597953479836694502607459 84896930219755041753911189)
          ·
            refine ⟨3979543604051017582214587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84896930219755041753911189 3979543604051017582214587)
            ·
              refine ⟨5969315406076526373321881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3979543604051017582214587 5969315406076526373321881)
              ·
                refine ⟨4476986554557394779991411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5969315406076526373321881 4476986554557394779991411)
                ·
                  refine ⟨6715479831836092169987117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476986554557394779991411 6715479831836092169987117)
                  ·
                    refine ⟨2518304936938534563745169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6715479831836092169987117 2518304936938534563745169)
                    ·
                      refine ⟨1888728702703900922808877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518304936938534563745169 1888728702703900922808877)
                      ·
                        rfl

theorem cell23_3678286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_3678286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678286 prefixEnd_3678286 := by exact prefixLift 3678286
  have htrace : WordTrace (prefixWord ++ tailWord_3678286) baseStart_3678286 baseEnd_3678286 := by
    simpa [prefixWord, tailWord_3678286, baseEnd_3678286] using wordTrace_append hprefix tailTrace_3678286
  have hstable : (prefixWord ++ tailWord_3678286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678286).length < 2 ^ (prefixWord ++ tailWord_3678286).sum := by decide
  have hdescent : baseEnd_3678286 < baseStart_3678286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678316 : List Nat := [2, 2, 1, 1, 3, 4, 2, 2, 2, 2, 2]
def baseStart_3678316 : Nat := 118140960795 + 3678316 * 2 ^ 59
def prefixEnd_3678316 : Nat := 4983230072969 + 3 ^ 40 * 3678316 * 2
def baseEnd_3678316 : Nat := 1888744107123535805433739

theorem tailTrace_3678316 : CollatzResearch.WordTrace tailWord_3678316 prefixEnd_3678316 1888744107123535805433739 := by
  unfold tailWord_3678316
  simp only [CollatzResearch.WordTrace]
  refine ⟨67079603071048406601923401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89439470761397875469231201 67079603071048406601923401)
  ·
    refine ⟨50309702303286304951442551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67079603071048406601923401 50309702303286304951442551)
    ·
      refine ⟨75464553454929457427163827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50309702303286304951442551 75464553454929457427163827)
      ·
        refine ⟨113196830182394186140745741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75464553454929457427163827 113196830182394186140745741)
        ·
          refine ⟨42448811318397819802779653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113196830182394186140745741 42448811318397819802779653)
          ·
            refine ⟨7959152122199591213021185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42448811318397819802779653 7959152122199591213021185)
            ·
              refine ⟨5969364091649693409765889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7959152122199591213021185 5969364091649693409765889)
              ·
                refine ⟨4477023068737270057324417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5969364091649693409765889 4477023068737270057324417)
                ·
                  refine ⟨3357767301552952542993313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4477023068737270057324417 3357767301552952542993313)
                  ·
                    refine ⟨2518325476164714407244985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3357767301552952542993313 2518325476164714407244985)
                    ·
                      refine ⟨1888744107123535805433739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518325476164714407244985 1888744107123535805433739)
                      ·
                        rfl

theorem cell23_3678316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 2, 2].length) (baseStart_3678316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678316 prefixEnd_3678316 := by exact prefixLift 3678316
  have htrace : WordTrace (prefixWord ++ tailWord_3678316) baseStart_3678316 baseEnd_3678316 := by
    simpa [prefixWord, tailWord_3678316, baseEnd_3678316] using wordTrace_append hprefix tailTrace_3678316
  have hstable : (prefixWord ++ tailWord_3678316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678316).length < 2 ^ (prefixWord ++ tailWord_3678316).sum := by decide
  have hdescent : baseEnd_3678316 < baseStart_3678316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678332 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 2, 3, 3]
def baseStart_3678332 : Nat := 118140960795 + 3678332 * 2 ^ 59
def prefixEnd_3678332 : Nat := 4983230072969 + 3 ^ 40 * 3678332 * 2
def baseEnd_3678332 : Nat := 1888752322814007742833665

theorem tailTrace_3678332 : CollatzResearch.WordTrace tailWord_3678332 prefixEnd_3678332 1888752322814007742833665 := by
  unfold tailWord_3678332
  simp only [CollatzResearch.WordTrace]
  refine ⟨67079894855019423968214625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89439859806692565290952833 67079894855019423968214625)
  ·
    refine ⟨50309921141264567976160969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67079894855019423968214625 50309921141264567976160969)
    ·
      refine ⟨37732440855948425982120727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50309921141264567976160969 37732440855948425982120727)
      ·
        refine ⟨56598661283922638973181091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37732440855948425982120727 56598661283922638973181091)
        ·
          refine ⟨84897991925883958459771637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56598661283922638973181091 84897991925883958459771637)
          ·
            refine ⟨7959186743051621105603591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84897991925883958459771637 7959186743051621105603591)
            ·
              refine ⟨11938780114577431658405387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7959186743051621105603591 11938780114577431658405387)
              ·
                refine ⟨17908170171866147487608081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11938780114577431658405387 17908170171866147487608081)
                ·
                  refine ⟨13431127628899610615706061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17908170171866147487608081 13431127628899610615706061)
                  ·
                    refine ⟨5036672860837353980889773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13431127628899610615706061 5036672860837353980889773)
                    ·
                      refine ⟨1888752322814007742833665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5036672860837353980889773 1888752322814007742833665)
                      ·
                        rfl

theorem cell23_3678332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_3678332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678332 prefixEnd_3678332 := by exact prefixLift 3678332
  have htrace : WordTrace (prefixWord ++ tailWord_3678332) baseStart_3678332 baseEnd_3678332 := by
    simpa [prefixWord, tailWord_3678332, baseEnd_3678332] using wordTrace_append hprefix tailTrace_3678332
  have hstable : (prefixWord ++ tailWord_3678332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678332).length < 2 ^ (prefixWord ++ tailWord_3678332).sum := by decide
  have hdescent : baseEnd_3678332 < baseStart_3678332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678442 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 3, 5]
def baseStart_3678442 : Nat := 118140960795 + 3678442 * 2 ^ 59
def prefixEnd_3678442 : Nat := 4983230072969 + 3 ^ 40 * 3678442 * 2
def baseEnd_3678442 : Nat := 629602935228667437486053

theorem tailTrace_3678442 : CollatzResearch.WordTrace tailWord_3678442 prefixEnd_3678442 629602935228667437486053 := by
  unfold tailWord_3678442
  simp only [CollatzResearch.WordTrace]
  refine ⟨33540950434910084180733395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89442534493093557815289053 33540950434910084180733395)
  ·
    refine ⟨50311425652365126271100093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33540950434910084180733395 50311425652365126271100093)
    ·
      refine ⟨18866784619636922351662535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50311425652365126271100093 18866784619636922351662535)
      ·
        refine ⟨28300176929455383527493803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18866784619636922351662535 28300176929455383527493803)
        ·
          refine ⟨42450265394183075291240705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28300176929455383527493803 42450265394183075291240705)
          ·
            refine ⟨31837699045637306468430529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42450265394183075291240705 31837699045637306468430529)
            ·
              refine ⟨23878274284227979851322897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31837699045637306468430529 23878274284227979851322897)
              ·
                refine ⟨17908705713170984888492173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23878274284227979851322897 17908705713170984888492173)
                ·
                  refine ⟨6715764642439119333184565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17908705713170984888492173 6715764642439119333184565)
                  ·
                    refine ⟨629602935228667437486053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6715764642439119333184565 629602935228667437486053)
                    ·
                      rfl

theorem cell23_3678442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_3678442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678442 prefixEnd_3678442 := by exact prefixLift 3678442
  have htrace : WordTrace (prefixWord ++ tailWord_3678442) baseStart_3678442 baseEnd_3678442 := by
    simpa [prefixWord, tailWord_3678442, baseEnd_3678442] using wordTrace_append hprefix tailTrace_3678442
  have hstable : (prefixWord ++ tailWord_3678442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678442).length < 2 ^ (prefixWord ++ tailWord_3678442).sum := by decide
  have hdescent : baseEnd_3678442 < baseStart_3678442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678472 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 3, 6]
def baseStart_3678472 : Nat := 118140960795 + 3678472 * 2 ^ 59
def prefixEnd_3678472 : Nat := 4983230072969 + 3 ^ 40 * 3678472 * 2
def baseEnd_3678472 : Nat := 629608070035212398361007

theorem tailTrace_3678472 : CollatzResearch.WordTrace tailWord_3678472 prefixEnd_3678472 629608070035212398361007 := by
  unfold tailWord_3678472
  simp only [CollatzResearch.WordTrace]
  refine ⟨67082447964765825923262835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89443263953021101231017113 67082447964765825923262835)
  ·
    refine ⟨100623671947148738884894253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67082447964765825923262835 100623671947148738884894253)
    ·
      refine ⟨37733876980180777081835345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100623671947148738884894253 37733876980180777081835345)
      ·
        refine ⟨28300407735135582811376509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37733876980180777081835345 28300407735135582811376509)
        ·
          refine ⟨10612652900675843554266191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28300407735135582811376509 10612652900675843554266191)
          ·
            refine ⟨15918979351013765331399287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10612652900675843554266191 15918979351013765331399287)
            ·
              refine ⟨23878469026520647997098931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15918979351013765331399287 23878469026520647997098931)
              ·
                refine ⟨35817703539780971995648397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23878469026520647997098931 35817703539780971995648397)
                ·
                  refine ⟨13431638827417864498368149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35817703539780971995648397 13431638827417864498368149)
                  ·
                    refine ⟨629608070035212398361007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13431638827417864498368149 629608070035212398361007)
                    ·
                      rfl

theorem cell23_3678472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_3678472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678472 prefixEnd_3678472 := by exact prefixLift 3678472
  have htrace : WordTrace (prefixWord ++ tailWord_3678472) baseStart_3678472 baseEnd_3678472 := by
    simpa [prefixWord, tailWord_3678472, baseEnd_3678472] using wordTrace_append hprefix tailTrace_3678472
  have hstable : (prefixWord ++ tailWord_3678472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678472).length < 2 ^ (prefixWord ++ tailWord_3678472).sum := by decide
  have hdescent : baseEnd_3678472 < baseStart_3678472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678492 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_3678492 : Nat := 118140960795 + 3678492 * 2 ^ 59
def prefixEnd_3678492 : Nat := 4983230072969 + 3 ^ 40 * 3678492 * 2
def baseEnd_3678492 : Nat := 1888834479718727116832929

theorem tailTrace_3678492 : CollatzResearch.WordTrace tailWord_3678492 prefixEnd_3678492 1888834479718727116832929 := by
  unfold tailWord_3678492
  simp only [CollatzResearch.WordTrace]
  refine ⟨67082812694729597631126865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89443750259639463508169153 67082812694729597631126865)
  ·
    refine ⟨50312109521047198223345149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67082812694729597631126865 50312109521047198223345149)
    ·
      refine ⟨18867041070392699333754431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50312109521047198223345149 18867041070392699333754431)
      ·
        refine ⟨28300561605589049000631647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18867041070392699333754431 28300561605589049000631647)
        ·
          refine ⟨42450842408383573500947471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28300561605589049000631647 42450842408383573500947471)
          ·
            refine ⟨63676263612575360251421207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42450842408383573500947471 63676263612575360251421207)
            ·
              refine ⟨95514395418863040377131811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63676263612575360251421207 95514395418863040377131811)
              ·
                refine ⟨143271593128294560565697717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95514395418863040377131811 143271593128294560565697717)
                ·
                  refine ⟨13431711855777615053034161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143271593128294560565697717 13431711855777615053034161)
                  ·
                    refine ⟨10073783891833211289775621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13431711855777615053034161 10073783891833211289775621)
                    ·
                      refine ⟨1888834479718727116832929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10073783891833211289775621 1888834479718727116832929)
                      ·
                        rfl

theorem cell23_3678492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_3678492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678492 prefixEnd_3678492 := by exact prefixLift 3678492
  have htrace : WordTrace (prefixWord ++ tailWord_3678492) baseStart_3678492 baseEnd_3678492 := by
    simpa [prefixWord, tailWord_3678492, baseEnd_3678492] using wordTrace_append hprefix tailTrace_3678492
  have hstable : (prefixWord ++ tailWord_3678492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678492).length < 2 ^ (prefixWord ++ tailWord_3678492).sum := by decide
  have hdescent : baseEnd_3678492 < baseStart_3678492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678506 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 1, 6]
def baseStart_3678506 : Nat := 118140960795 + 3678506 * 2 ^ 59
def prefixEnd_3678506 : Nat := 4983230072969 + 3 ^ 40 * 3678506 * 2
def baseEnd_3678506 : Nat := 629613889482630020685955

theorem tailTrace_3678506 : CollatzResearch.WordTrace tailWord_3678506 prefixEnd_3678506 629613889482630020685955 := by
  unfold tailWord_3678506
  simp only [CollatzResearch.WordTrace]
  refine ⟨33541534002852118913315843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89444090674272317102175581 33541534002852118913315843)
  ·
    refine ⟨50312301004278178369973765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33541534002852118913315843 50312301004278178369973765)
    ·
      refine ⟨9433556438302158444370081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50312301004278178369973765 9433556438302158444370081)
      ·
        refine ⟨7075167328726618833277561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9433556438302158444370081 7075167328726618833277561)
        ·
          refine ⟨5306375496544964124958171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7075167328726618833277561 5306375496544964124958171)
          ·
            refine ⟨7959563244817446187437257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306375496544964124958171 7959563244817446187437257)
            ·
              refine ⟨5969672433613084640577943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7959563244817446187437257 5969672433613084640577943)
              ·
                refine ⟨8954508650419626960866915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5969672433613084640577943 8954508650419626960866915)
                ·
                  refine ⟨13431762975629440441300373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8954508650419626960866915 13431762975629440441300373)
                  ·
                    refine ⟨629613889482630020685955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13431762975629440441300373 629613889482630020685955)
                    ·
                      rfl

theorem cell23_3678506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_3678506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678506 prefixEnd_3678506 := by exact prefixLift 3678506
  have htrace : WordTrace (prefixWord ++ tailWord_3678506) baseStart_3678506 baseEnd_3678506 := by
    simpa [prefixWord, tailWord_3678506, baseEnd_3678506] using wordTrace_append hprefix tailTrace_3678506
  have hstable : (prefixWord ++ tailWord_3678506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678506).length < 2 ^ (prefixWord ++ tailWord_3678506).sum := by decide
  have hdescent : baseEnd_3678506 < baseStart_3678506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678513 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 3, 2, 2]
def baseStart_3678513 : Nat := 118140960795 + 3678513 * 2 ^ 59
def prefixEnd_3678513 : Nat := 4983230072969 + 3 ^ 40 * 3678513 * 2
def baseEnd_3678513 : Nat := 1888845262812471534670333

theorem tailTrace_3678513 : CollatzResearch.WordTrace tailWord_3678513 prefixEnd_3678513 1888845262812471534670333 := by
  unfold tailWord_3678513
  simp only [CollatzResearch.WordTrace]
  refine ⟨134166391322383115848768193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89444260881588743899178795 134166391322383115848768193)
  ·
    refine ⟨100624793491787336886576145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134166391322383115848768193 100624793491787336886576145)
    ·
      refine ⟨75468595118840502664932109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100624793491787336886576145 75468595118840502664932109)
      ·
        refine ⟨28300723169565188499349541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75468595118840502664932109 28300723169565188499349541)
        ·
          refine ⟨5306385594293472843628039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28300723169565188499349541 5306385594293472843628039)
          ·
            refine ⟨7959578391440209265442059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306385594293472843628039 7959578391440209265442059)
            ·
              refine ⟨11939367587160313898163089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7959578391440209265442059 11939367587160313898163089)
              ·
                refine ⟨8954525690370235423622317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11939367587160313898163089 8954525690370235423622317)
                ·
                  refine ⟨3357947133888838283858369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8954525690370235423622317 3357947133888838283858369)
                  ·
                    refine ⟨2518460350416628712893777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3357947133888838283858369 2518460350416628712893777)
                    ·
                      refine ⟨1888845262812471534670333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518460350416628712893777 1888845262812471534670333)
                      ·
                        rfl

theorem cell23_3678513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_3678513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678513 prefixEnd_3678513 := by exact prefixLift 3678513
  have htrace : WordTrace (prefixWord ++ tailWord_3678513) baseStart_3678513 baseEnd_3678513 := by
    simpa [prefixWord, tailWord_3678513, baseEnd_3678513] using wordTrace_append hprefix tailTrace_3678513
  have hstable : (prefixWord ++ tailWord_3678513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678513).length < 2 ^ (prefixWord ++ tailWord_3678513).sum := by decide
  have hdescent : baseEnd_3678513 < baseStart_3678513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678516 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_3678516 : Nat := 118140960795 + 3678516 * 2 ^ 59
def prefixEnd_3678516 : Nat := 4983230072969 + 3 ^ 40 * 3678516 * 2
def baseEnd_3678516 : Nat := 1888846803254435022932819

theorem tailTrace_3678516 : CollatzResearch.WordTrace tailWord_3678516 prefixEnd_3678516 1888846803254435022932819 := by
  unfold tailWord_3678516
  simp only [CollatzResearch.WordTrace]
  refine ⟨67083250370686123680563701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89444333827581498240751601 67083250370686123680563701)
  ·
    refine ⟨6289054722251824095052847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67083250370686123680563701 6289054722251824095052847)
    ·
      refine ⟨9433582083377736142579271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6289054722251824095052847 9433582083377736142579271)
      ·
        refine ⟨14150373125066604213868907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9433582083377736142579271 14150373125066604213868907)
        ·
          refine ⟨21225559687599906320803361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14150373125066604213868907 21225559687599906320803361)
          ·
            refine ⟨15919169765699929740602521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21225559687599906320803361 15919169765699929740602521)
            ·
              refine ⟨11939377324274947305451891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15919169765699929740602521 11939377324274947305451891)
              ·
                refine ⟨17909065986412420958177837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11939377324274947305451891 17909065986412420958177837)
                ·
                  refine ⟨6715899744904657859316689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17909065986412420958177837 6715899744904657859316689)
                  ·
                    refine ⟨5036924808678493394487517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6715899744904657859316689 5036924808678493394487517)
                    ·
                      refine ⟨1888846803254435022932819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5036924808678493394487517 1888846803254435022932819)
                      ·
                        rfl

theorem cell23_3678516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_3678516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678516 prefixEnd_3678516 := by exact prefixLift 3678516
  have htrace : WordTrace (prefixWord ++ tailWord_3678516) baseStart_3678516 baseEnd_3678516 := by
    simpa [prefixWord, tailWord_3678516, baseEnd_3678516] using wordTrace_append hprefix tailTrace_3678516
  have hstable : (prefixWord ++ tailWord_3678516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678516).length < 2 ^ (prefixWord ++ tailWord_3678516).sum := by decide
  have hdescent : baseEnd_3678516 < baseStart_3678516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678539 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 5, 3, 2]
def baseStart_3678539 : Nat := 118140960795 + 3678539 * 2 ^ 59
def prefixEnd_3678539 : Nat := 4983230072969 + 3 ^ 40 * 3678539 * 2
def baseEnd_3678539 : Nat := 1888858613309488432945213

theorem tailTrace_3678539 : CollatzResearch.WordTrace tailWord_3678539 prefixEnd_3678539 1888858613309488432945213 := by
  unfold tailWord_3678539
  simp only [CollatzResearch.WordTrace]
  refine ⟨134167339620288922289214671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89444893080192614859476447 134167339620288922289214671)
  ·
    refine ⟨201251009430433383433822007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134167339620288922289214671 201251009430433383433822007)
    ·
      refine ⟨301876514145650075150733011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201251009430433383433822007 301876514145650075150733011)
      ·
        refine ⟨452814771218475112726099517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301876514145650075150733011 452814771218475112726099517)
        ·
          refine ⟨169805539206928167272287319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 452814771218475112726099517 169805539206928167272287319)
          ·
            refine ⟨254708308810392250908430979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169805539206928167272287319 254708308810392250908430979)
            ·
              refine ⟨382062463215588376362646469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254708308810392250908430979 382062463215588376362646469)
              ·
                refine ⟨71636711852922820567996213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 382062463215588376362646469 71636711852922820567996213)
                ·
                  refine ⟨6715941736211514428249645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71636711852922820567996213 6715941736211514428249645)
                  ·
                    refine ⟨2518478151079317910593617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6715941736211514428249645 2518478151079317910593617)
                    ·
                      refine ⟨1888858613309488432945213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518478151079317910593617 1888858613309488432945213)
                      ·
                        rfl

theorem cell23_3678539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 3, 2].length) (baseStart_3678539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678539 prefixEnd_3678539 := by exact prefixLift 3678539
  have htrace : WordTrace (prefixWord ++ tailWord_3678539) baseStart_3678539 baseEnd_3678539 := by
    simpa [prefixWord, tailWord_3678539, baseEnd_3678539] using wordTrace_append hprefix tailTrace_3678539
  have hstable : (prefixWord ++ tailWord_3678539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678539).length < 2 ^ (prefixWord ++ tailWord_3678539).sum := by decide
  have hdescent : baseEnd_3678539 < baseStart_3678539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678542 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_3678542 : Nat := 118140960795 + 3678542 * 2 ^ 59
def prefixEnd_3678542 : Nat := 4983230072969 + 3 ^ 40 * 3678542 * 2
def baseEnd_3678542 : Nat := 1888860153751451921207699

theorem tailTrace_3678542 : CollatzResearch.WordTrace tailWord_3678542 prefixEnd_3678542 1888860153751451921207699 := by
  unfold tailWord_3678542
  simp only [CollatzResearch.WordTrace]
  refine ⟨16770931129909756725196735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89444966026185369201049253 16770931129909756725196735)
  ·
    refine ⟨25156396694864635087795103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16770931129909756725196735 25156396694864635087795103)
    ·
      refine ⟨37734595042296952631692655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25156396694864635087795103 37734595042296952631692655)
      ·
        refine ⟨56601892563445428947538983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37734595042296952631692655 56601892563445428947538983)
        ·
          refine ⟨84902838845168143421308475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56601892563445428947538983 84902838845168143421308475)
          ·
            refine ⟨127354258267752215131962713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84902838845168143421308475 127354258267752215131962713)
            ·
              refine ⟨95515693700814161348972035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127354258267752215131962713 95515693700814161348972035)
              ·
                refine ⟨143273540551221242023458053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95515693700814161348972035 143273540551221242023458053)
                ·
                  refine ⟨26863788853353982879398385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143273540551221242023458053 26863788853353982879398385)
                  ·
                    refine ⟨20147841640015487159548789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26863788853353982879398385 20147841640015487159548789)
                    ·
                      refine ⟨1888860153751451921207699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20147841640015487159548789 1888860153751451921207699)
                      ·
                        rfl

theorem cell23_3678542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_3678542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678542 prefixEnd_3678542 := by exact prefixLift 3678542
  have htrace : WordTrace (prefixWord ++ tailWord_3678542) baseStart_3678542 baseEnd_3678542 := by
    simpa [prefixWord, tailWord_3678542, baseEnd_3678542] using wordTrace_append hprefix tailTrace_3678542
  have hstable : (prefixWord ++ tailWord_3678542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678542).length < 2 ^ (prefixWord ++ tailWord_3678542).sum := by decide
  have hdescent : baseEnd_3678542 < baseStart_3678542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678552 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 2, 3, 4]
def baseStart_3678552 : Nat := 118140960795 + 3678552 * 2 ^ 59
def prefixEnd_3678552 : Nat := 4983230072969 + 3 ^ 40 * 3678552 * 2
def baseEnd_3678552 : Nat := 1888865288557996882082653

theorem tailTrace_3678552 : CollatzResearch.WordTrace tailWord_3678552 prefixEnd_3678552 1888865288557996882082653 := by
  unfold tailWord_3678552
  simp only [CollatzResearch.WordTrace]
  refine ⟨67083906884620912754718955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89445209179494550339625273 67083906884620912754718955)
  ·
    refine ⟨100625860326931369132078433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67083906884620912754718955 100625860326931369132078433)
    ·
      refine ⟨75469395245198526849058825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100625860326931369132078433 75469395245198526849058825)
      ·
        refine ⟨56602046433898895136794119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75469395245198526849058825 56602046433898895136794119)
        ·
          refine ⟨84903069650848342705191179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56602046433898895136794119 84903069650848342705191179)
          ·
            refine ⟨127354604476272514057786769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84903069650848342705191179 127354604476272514057786769)
            ·
              refine ⟨95515953357204385543340077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127354604476272514057786769 95515953357204385543340077)
              ·
                refine ⟨35818482508951644578752529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95515953357204385543340077 35818482508951644578752529)
                ·
                  refine ⟨26863861881713733434064397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35818482508951644578752529 26863861881713733434064397)
                  ·
                    refine ⟨10073948205642650037774149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26863861881713733434064397 10073948205642650037774149)
                    ·
                      refine ⟨1888865288557996882082653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10073948205642650037774149 1888865288557996882082653)
                      ·
                        rfl

theorem cell23_3678552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_3678552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678552 prefixEnd_3678552 := by exact prefixLift 3678552
  have htrace : WordTrace (prefixWord ++ tailWord_3678552) baseStart_3678552 baseEnd_3678552 := by
    simpa [prefixWord, tailWord_3678552, baseEnd_3678552] using wordTrace_append hprefix tailTrace_3678552
  have hstable : (prefixWord ++ tailWord_3678552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678552).length < 2 ^ (prefixWord ++ tailWord_3678552).sum := by decide
  have hdescent : baseEnd_3678552 < baseStart_3678552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678563 : List Nat := [1, 1, 1, 5, 2, 1, 5, 1, 2, 1, 3]
def baseStart_3678563 : Nat := 118140960795 + 3678563 * 2 ^ 59
def prefixEnd_3678563 : Nat := 4983230072969 + 3 ^ 40 * 3678563 * 2
def baseEnd_3678563 : Nat := 1888870936845196339045103

theorem tailTrace_3678563 : CollatzResearch.WordTrace tailWord_3678563 prefixEnd_3678563 1888870936845196339045103 := by
  unfold tailWord_3678563
  simp only [CollatzResearch.WordTrace]
  refine ⟨134168214972201974388088343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89445476648134649592058895 134168214972201974388088343)
  ·
    refine ⟨201252322458302961582132515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134168214972201974388088343 201252322458302961582132515)
    ·
      refine ⟨301878483687454442373198773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201252322458302961582132515 301878483687454442373198773)
      ·
        refine ⟨28301107845698853972487385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 301878483687454442373198773 28301107845698853972487385)
        ·
          refine ⟨21225830884274140479365539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28301107845698853972487385 21225830884274140479365539)
          ·
            refine ⟨31838746326411210719048309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21225830884274140479365539 31838746326411210719048309)
            ·
              refine ⟨2984882468101051004910779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31838746326411210719048309 2984882468101051004910779)
              ·
                refine ⟨4477323702151576507366169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984882468101051004910779 4477323702151576507366169)
                ·
                  refine ⟨3357992776613682380524627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4477323702151576507366169 3357992776613682380524627)
                  ·
                    refine ⟨5036989164920523570786941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3357992776613682380524627 5036989164920523570786941)
                    ·
                      refine ⟨1888870936845196339045103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5036989164920523570786941 1888870936845196339045103)
                      ·
                        rfl

theorem cell23_3678563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_3678563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678563 prefixEnd_3678563 := by exact prefixLift 3678563
  have htrace : WordTrace (prefixWord ++ tailWord_3678563) baseStart_3678563 baseEnd_3678563 := by
    simpa [prefixWord, tailWord_3678563, baseEnd_3678563] using wordTrace_append hprefix tailTrace_3678563
  have hstable : (prefixWord ++ tailWord_3678563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678563).length < 2 ^ (prefixWord ++ tailWord_3678563).sum := by decide
  have hdescent : baseEnd_3678563 < baseStart_3678563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678573 : List Nat := [1, 5, 1, 1, 1, 2, 4, 2, 1, 3, 2]
def baseStart_3678573 : Nat := 118140960795 + 3678573 * 2 ^ 59
def prefixEnd_3678573 : Nat := 4983230072969 + 3 ^ 40 * 3678573 * 2
def baseEnd_3678573 : Nat := 1888876071651741299920057

theorem tailTrace_3678573 : CollatzResearch.WordTrace tailWord_3678573 prefixEnd_3678573 1888876071651741299920057 := by
  unfold tailWord_3678573
  simp only [CollatzResearch.WordTrace]
  refine ⟨134168579702165746095952373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89445719801443830730634915 134168579702165746095952373)
  ·
    refine ⟨12578304347078038696495535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134168579702165746095952373 12578304347078038696495535)
    ·
      refine ⟨18867456520617058044743303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12578304347078038696495535 18867456520617058044743303)
      ·
        refine ⟨28301184780925587067114955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18867456520617058044743303 28301184780925587067114955)
        ·
          refine ⟨42451777171388380600672433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28301184780925587067114955 42451777171388380600672433)
          ·
            refine ⟨31838832878541285450504325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42451777171388380600672433 31838832878541285450504325)
            ·
              refine ⟨5969781164726491021969561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31838832878541285450504325 5969781164726491021969561)
              ·
                refine ⟨4477335873544868266477171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5969781164726491021969561 4477335873544868266477171)
                ·
                  refine ⟨6716003810317302399715757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4477335873544868266477171 6716003810317302399715757)
                  ·
                    refine ⟨2518501428868988399893409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6716003810317302399715757 2518501428868988399893409)
                    ·
                      refine ⟨1888876071651741299920057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518501428868988399893409 1888876071651741299920057)
                      ·
                        rfl

theorem cell23_3678573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_3678573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678573 prefixEnd_3678573 := by exact prefixLift 3678573
  have htrace : WordTrace (prefixWord ++ tailWord_3678573) baseStart_3678573 baseEnd_3678573 := by
    simpa [prefixWord, tailWord_3678573, baseEnd_3678573] using wordTrace_append hprefix tailTrace_3678573
  have hstable : (prefixWord ++ tailWord_3678573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678573).length < 2 ^ (prefixWord ++ tailWord_3678573).sum := by decide
  have hdescent : baseEnd_3678573 < baseStart_3678573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678589 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_3678589 : Nat := 118140960795 + 3678589 * 2 ^ 59
def prefixEnd_3678589 : Nat := 4983230072969 + 3 ^ 40 * 3678589 * 2
def baseEnd_3678589 : Nat := 1888884287342213237319983

theorem tailTrace_3678589 : CollatzResearch.WordTrace tailWord_3678589 prefixEnd_3678589 1888884287342213237319983 := by
  unfold tailWord_3678589
  simp only [CollatzResearch.WordTrace]
  refine ⟨134169163270107780828534821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89446108846738520552356547 134169163270107780828534821)
  ·
    refine ⟨25156718113145208905350279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134169163270107780828534821 25156718113145208905350279)
    ·
      refine ⟨37735077169717813358025419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25156718113145208905350279 37735077169717813358025419)
      ·
        refine ⟨56602615754576720037038129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37735077169717813358025419 56602615754576720037038129)
        ·
          refine ⟨42451961815932540027778597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56602615754576720037038129 42451961815932540027778597)
          ·
            refine ⟨7959742840487351255208487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42451961815932540027778597 7959742840487351255208487)
            ·
              refine ⟨11939614260731026882812731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7959742840487351255208487 11939614260731026882812731)
              ·
                refine ⟨17909421391096540324219097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11939614260731026882812731 17909421391096540324219097)
                ·
                  refine ⟨13432066043322405243164323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17909421391096540324219097 13432066043322405243164323)
                  ·
                    refine ⟨20148099064983607864746485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13432066043322405243164323 20148099064983607864746485)
                    ·
                      refine ⟨1888884287342213237319983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20148099064983607864746485 1888884287342213237319983)
                      ·
                        rfl

theorem cell23_3678589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_3678589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678589 prefixEnd_3678589 := by exact prefixLift 3678589
  have htrace : WordTrace (prefixWord ++ tailWord_3678589) baseStart_3678589 baseEnd_3678589 := by
    simpa [prefixWord, tailWord_3678589, baseEnd_3678589] using wordTrace_append hprefix tailTrace_3678589
  have hstable : (prefixWord ++ tailWord_3678589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678589).length < 2 ^ (prefixWord ++ tailWord_3678589).sum := by decide
  have hdescent : baseEnd_3678589 < baseStart_3678589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678614 : List Nat := [5, 3, 1, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3678614 : Nat := 118140960795 + 3678614 * 2 ^ 59
def prefixEnd_3678614 : Nat := 4983230072969 + 3 ^ 40 * 3678614 * 2
def baseEnd_3678614 : Nat := 1888897124358575639507369

theorem tailTrace_3678614 : CollatzResearch.WordTrace tailWord_3678614 prefixEnd_3678614 1888897124358575639507369 := by
  unfold tailWord_3678614
  simp only [CollatzResearch.WordTrace]
  refine ⟨8385629693438575631137181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89446716730011473398796597 8385629693438575631137181)
  ·
    refine ⟨3144611135039465861676443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8385629693438575631137181 3144611135039465861676443)
    ·
      refine ⟨4716916702559198792514665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3144611135039465861676443 4716916702559198792514665)
      ·
        refine ⟨3537687526919399094385999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4716916702559198792514665 3537687526919399094385999)
        ·
          refine ⟨5306531290379098641578999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3537687526919399094385999 5306531290379098641578999)
          ·
            refine ⟨7959796935568647962368499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306531290379098641578999 7959796935568647962368499)
            ·
              refine ⟨11939695403352971943552749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7959796935568647962368499 11939695403352971943552749)
              ·
                refine ⟨4477385776257364478832281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11939695403352971943552749 4477385776257364478832281)
                ·
                  refine ⟨3358039332193023359124211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4477385776257364478832281 3358039332193023359124211)
                  ·
                    refine ⟨5037058998289535038686317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3358039332193023359124211 5037058998289535038686317)
                    ·
                      refine ⟨1888897124358575639507369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5037058998289535038686317 1888897124358575639507369)
                      ·
                        rfl

theorem cell23_3678614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3678614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678614 prefixEnd_3678614 := by exact prefixLift 3678614
  have htrace : WordTrace (prefixWord ++ tailWord_3678614) baseStart_3678614 baseEnd_3678614 := by
    simpa [prefixWord, tailWord_3678614, baseEnd_3678614] using wordTrace_append hprefix tailTrace_3678614
  have hstable : (prefixWord ++ tailWord_3678614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678614).length < 2 ^ (prefixWord ++ tailWord_3678614).sum := by decide
  have hdescent : baseEnd_3678614 < baseStart_3678614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678649 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 1, 2, 5]
def baseStart_3678649 : Nat := 118140960795 + 3678649 * 2 ^ 59
def prefixEnd_3678649 : Nat := 4983230072969 + 3 ^ 40 * 3678649 * 2
def baseEnd_3678649 : Nat := 1888915096181483002569707

theorem tailTrace_3678649 : CollatzResearch.WordTrace tailWord_3678649 prefixEnd_3678649 1888915096181483002569707 := by
  unfold tailWord_3678649
  simp only [CollatzResearch.WordTrace]
  refine ⟨134171351649890411075719001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89447567766593607383812667 134171351649890411075719001)
  ·
    refine ⟨100628513737417808306789251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134171351649890411075719001 100628513737417808306789251)
    ·
      refine ⟨150942770606126712460183877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100628513737417808306789251 150942770606126712460183877)
      ·
        refine ⟨28301769488648758586284477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150942770606126712460183877 28301769488648758586284477)
        ·
          refine ⟨10613163558243284469856679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28301769488648758586284477 10613163558243284469856679)
          ·
            refine ⟨15919745337364926704785019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10613163558243284469856679 15919745337364926704785019)
            ·
              refine ⟨23879618006047390057177529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15919745337364926704785019 23879618006047390057177529)
              ·
                refine ⟨17909713504535542542883147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23879618006047390057177529 17909713504535542542883147)
                ·
                  refine ⟨26864570256803313814324721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17909713504535542542883147 26864570256803313814324721)
                  ·
                    refine ⟨20148427692602485360743541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26864570256803313814324721 20148427692602485360743541)
                    ·
                      refine ⟨1888915096181483002569707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20148427692602485360743541 1888915096181483002569707)
                      ·
                        rfl

theorem cell23_3678649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_3678649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678649 prefixEnd_3678649 := by exact prefixLift 3678649
  have htrace : WordTrace (prefixWord ++ tailWord_3678649) baseStart_3678649 baseEnd_3678649 := by
    simpa [prefixWord, tailWord_3678649, baseEnd_3678649] using wordTrace_append hprefix tailTrace_3678649
  have hstable : (prefixWord ++ tailWord_3678649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678649).length < 2 ^ (prefixWord ++ tailWord_3678649).sum := by decide
  have hdescent : baseEnd_3678649 < baseStart_3678649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678696 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_3678696 : Nat := 118140960795 + 3678696 * 2 ^ 59
def prefixEnd_3678696 : Nat := 4983230072969 + 3 ^ 40 * 3678696 * 2
def baseEnd_3678696 : Nat := 1888939229772244318681991

theorem tailTrace_3678696 : CollatzResearch.WordTrace tailWord_3678696 prefixEnd_3678696 1888939229772244318681991 := by
  unfold tailWord_3678696
  simp only [CollatzResearch.WordTrace]
  refine ⟨67086532940360069051339971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89448710587146758735119961 67086532940360069051339971)
  ·
    refine ⟨100629799410540103577009957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67086532940360069051339971 100629799410540103577009957)
    ·
      refine ⟨18868087389476269420689367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100629799410540103577009957 18868087389476269420689367)
      ·
        refine ⟨28302131084214404131034051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18868087389476269420689367 28302131084214404131034051)
        ·
          refine ⟨42453196626321606196551077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28302131084214404131034051 42453196626321606196551077)
          ·
            refine ⟨7959974367435301161853327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42453196626321606196551077 7959974367435301161853327)
            ·
              refine ⟨11939961551152951742779991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7959974367435301161853327 11939961551152951742779991)
              ·
                refine ⟨17909942326729427614169987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11939961551152951742779991 17909942326729427614169987)
                ·
                  refine ⟨26864913490094141421254981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17909942326729427614169987 26864913490094141421254981)
                  ·
                    refine ⟨5037171279392651516485309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26864913490094141421254981 5037171279392651516485309)
                    ·
                      refine ⟨1888939229772244318681991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5037171279392651516485309 1888939229772244318681991)
                      ·
                        rfl

theorem cell23_3678696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_3678696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678696 prefixEnd_3678696 := by exact prefixLift 3678696
  have htrace : WordTrace (prefixWord ++ tailWord_3678696) baseStart_3678696 baseEnd_3678696 := by
    simpa [prefixWord, tailWord_3678696, baseEnd_3678696] using wordTrace_append hprefix tailTrace_3678696
  have hstable : (prefixWord ++ tailWord_3678696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678696).length < 2 ^ (prefixWord ++ tailWord_3678696).sum := by decide
  have hdescent : baseEnd_3678696 < baseStart_3678696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678729 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 3, 5]
def baseStart_3678729 : Nat := 118140960795 + 3678729 * 2 ^ 59
def prefixEnd_3678729 : Nat := 4983230072969 + 3 ^ 40 * 3678729 * 2
def baseEnd_3678729 : Nat := 629652058211280896523113

theorem tailTrace_3678729 : CollatzResearch.WordTrace tailWord_3678729 prefixEnd_3678729 629652058211280896523113 := by
  unfold tailWord_3678729
  simp only [CollatzResearch.WordTrace]
  refine ⟨134174269489600584738631241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89449512993067056492420827 134174269489600584738631241)
  ·
    refine ⟨100630702117200438553973431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134174269489600584738631241 100630702117200438553973431)
    ·
      refine ⟨150946053175800657830960147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100630702117200438553973431 150946053175800657830960147)
      ·
        refine ⟨226419079763700986746440221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150946053175800657830960147 226419079763700986746440221)
        ·
          refine ⟨84907154911387870029915083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226419079763700986746440221 84907154911387870029915083)
          ·
            refine ⟨127360732367081805044872625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84907154911387870029915083 127360732367081805044872625)
            ·
              refine ⟨95520549275311353783654469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127360732367081805044872625 95520549275311353783654469)
              ·
                refine ⟨17910102989120878834435213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95520549275311353783654469 17910102989120878834435213)
                ·
                  refine ⟨6716288620920329562913205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17910102989120878834435213 6716288620920329562913205)
                  ·
                    refine ⟨629652058211280896523113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6716288620920329562913205 629652058211280896523113)
                    ·
                      rfl

theorem cell23_3678729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 5].length) (baseStart_3678729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678729 prefixEnd_3678729 := by exact prefixLift 3678729
  have htrace : WordTrace (prefixWord ++ tailWord_3678729) baseStart_3678729 baseEnd_3678729 := by
    simpa [prefixWord, tailWord_3678729, baseEnd_3678729] using wordTrace_append hprefix tailTrace_3678729
  have hstable : (prefixWord ++ tailWord_3678729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678729).length < 2 ^ (prefixWord ++ tailWord_3678729).sum := by decide
  have hdescent : baseEnd_3678729 < baseStart_3678729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678746 : List Nat := [3, 1, 1, 3, 1, 1, 3, 4, 1, 5]
def baseStart_3678746 : Nat := 118140960795 + 3678746 * 2 ^ 59
def prefixEnd_3678746 : Nat := 4983230072969 + 3 ^ 40 * 3678746 * 2
def baseEnd_3678746 : Nat := 629654967934989707685587

theorem tailTrace_3678746 : CollatzResearch.WordTrace tailWord_3678746 prefixEnd_3678746 629654967934989707685587 := by
  unfold tailWord_3678746
  simp only [CollatzResearch.WordTrace]
  refine ⟨33543722382634749160500023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89449926353692664428000061 33543722382634749160500023)
  ·
    refine ⟨50315583573952123740750035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33543722382634749160500023 50315583573952123740750035)
    ·
      refine ⟨75473375360928185611125053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50315583573952123740750035 75473375360928185611125053)
      ·
        refine ⟨28302515760348069604171895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75473375360928185611125053 28302515760348069604171895)
        ·
          refine ⟨42453773640522104406257843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28302515760348069604171895 42453773640522104406257843)
          ·
            refine ⟨63680660460783156609386765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42453773640522104406257843 63680660460783156609386765)
            ·
              refine ⟨23880247672793683728520037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63680660460783156609386765 23880247672793683728520037)
              ·
                refine ⟨4477546438648815699097507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23880247672793683728520037 4477546438648815699097507)
                ·
                  refine ⟨6716319657973223548646261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4477546438648815699097507 6716319657973223548646261)
                  ·
                    refine ⟨629654967934989707685587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6716319657973223548646261 629654967934989707685587)
                    ·
                      rfl

theorem cell23_3678746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_3678746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678746 prefixEnd_3678746 := by exact prefixLift 3678746
  have htrace : WordTrace (prefixWord ++ tailWord_3678746) baseStart_3678746 baseEnd_3678746 := by
    simpa [prefixWord, tailWord_3678746, baseEnd_3678746] using wordTrace_append hprefix tailTrace_3678746
  have hstable : (prefixWord ++ tailWord_3678746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678746).length < 2 ^ (prefixWord ++ tailWord_3678746).sum := by decide
  have hdescent : baseEnd_3678746 < baseStart_3678746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678753 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 2, 3, 2]
def baseStart_3678753 : Nat := 118140960795 + 3678753 * 2 ^ 59
def prefixEnd_3678753 : Nat := 4983230072969 + 3 ^ 40 * 3678753 * 2
def baseEnd_3678753 : Nat := 1888968498169550595669229

theorem tailTrace_3678753 : CollatzResearch.WordTrace tailWord_3678753 prefixEnd_3678753 1888968498169550595669229 := by
  unfold tailWord_3678753
  simp only [CollatzResearch.WordTrace]
  refine ⟨134175144841513636837504913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89450096561009091225003275 134175144841513636837504913)
  ·
    refine ⟨100631358631135227628128685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134175144841513636837504913 100631358631135227628128685)
    ·
      refine ⟨37736759486675710360548257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100631358631135227628128685 37736759486675710360548257)
      ·
        refine ⟨28302569615006782770411193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37736759486675710360548257 28302569615006782770411193)
        ·
          refine ⟨21226927211255087077808395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28302569615006782770411193 21226927211255087077808395)
          ·
            refine ⟨31840390816882630616712593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21226927211255087077808395 31840390816882630616712593)
            ·
              refine ⟨23880293112661972962534445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31840390816882630616712593 23880293112661972962534445)
              ·
                refine ⟨8955109917248239860950417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23880293112661972962534445 8955109917248239860950417)
                ·
                  refine ⟨6716332437936179895712813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8955109917248239860950417 6716332437936179895712813)
                  ·
                    refine ⟨2518624664226067460892305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6716332437936179895712813 2518624664226067460892305)
                    ·
                      refine ⟨1888968498169550595669229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518624664226067460892305 1888968498169550595669229)
                      ·
                        rfl

theorem cell23_3678753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_3678753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678753 prefixEnd_3678753 := by exact prefixLift 3678753
  have htrace : WordTrace (prefixWord ++ tailWord_3678753) baseStart_3678753 baseEnd_3678753 := by
    simpa [prefixWord, tailWord_3678753, baseEnd_3678753] using wordTrace_append hprefix tailTrace_3678753
  have hstable : (prefixWord ++ tailWord_3678753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678753).length < 2 ^ (prefixWord ++ tailWord_3678753).sum := by decide
  have hdescent : baseEnd_3678753 < baseStart_3678753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678776 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 4, 4]
def baseStart_3678776 : Nat := 118140960795 + 3678776 * 2 ^ 59
def prefixEnd_3678776 : Nat := 4983230072969 + 3 ^ 40 * 3678776 * 2
def baseEnd_3678776 : Nat := 629660102741534668560541

theorem tailTrace_3678776 : CollatzResearch.WordTrace tailWord_3678776 prefixEnd_3678776 629660102741534668560541 := by
  unfold tailWord_3678776
  simp only [CollatzResearch.WordTrace]
  refine ⟨67087991860215155882796091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89450655813620207843728121 67087991860215155882796091)
  ·
    refine ⟨100631987790322733824194137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67087991860215155882796091 100631987790322733824194137)
    ·
      refine ⟨75473990842742050368145603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100631987790322733824194137 75473990842742050368145603)
      ·
        refine ⟨113210986264113075552218405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75473990842742050368145603 113210986264113075552218405)
        ·
          refine ⟨21227059924521201666040951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113210986264113075552218405 21227059924521201666040951)
          ·
            refine ⟨31840589886781802499061427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21227059924521201666040951 31840589886781802499061427)
            ·
              refine ⟨47760884830172703748592141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31840589886781802499061427 47760884830172703748592141)
              ·
                refine ⟨17910331811314763905722053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47760884830172703748592141 17910331811314763905722053)
                ·
                  refine ⟨3358187214621518232322885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17910331811314763905722053 3358187214621518232322885)
                  ·
                    refine ⟨629660102741534668560541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3358187214621518232322885 629660102741534668560541)
                    ·
                      rfl

theorem cell23_3678776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_3678776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678776 prefixEnd_3678776 := by exact prefixLift 3678776
  have htrace : WordTrace (prefixWord ++ tailWord_3678776) baseStart_3678776 baseEnd_3678776 := by
    simpa [prefixWord, tailWord_3678776, baseEnd_3678776] using wordTrace_append hprefix tailTrace_3678776
  have hstable : (prefixWord ++ tailWord_3678776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678776).length < 2 ^ (prefixWord ++ tailWord_3678776).sum := by decide
  have hdescent : baseEnd_3678776 < baseStart_3678776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678777 : List Nat := [1, 2, 1, 5, 1, 1, 5, 2, 1, 1, 3]
def baseStart_3678777 : Nat := 118140960795 + 3678777 * 2 ^ 59
def prefixEnd_3678777 : Nat := 4983230072969 + 3 ^ 40 * 3678777 * 2
def baseEnd_3678777 : Nat := 1888980821705258501769119

theorem tailTrace_3678777 : CollatzResearch.WordTrace tailWord_3678777 prefixEnd_3678777 1888980821705258501769119 := by
  unfold tailWord_3678777
  simp only [CollatzResearch.WordTrace]
  refine ⟨134176020193426688936378585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89450680128951125957585723 134176020193426688936378585)
  ·
    refine ⟨100632015145070016702283939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134176020193426688936378585 100632015145070016702283939)
    ·
      refine ⟨150948022717605025053425909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100632015145070016702283939 150948022717605025053425909)
      ·
        refine ⟨14151377129775471098758679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150948022717605025053425909 14151377129775471098758679)
        ·
          refine ⟨21227065694663206648138019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14151377129775471098758679 21227065694663206648138019)
          ·
            refine ⟨31840598541994809972207029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21227065694663206648138019 31840598541994809972207029)
            ·
              refine ⟨2985056113312013434894409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31840598541994809972207029 2985056113312013434894409)
              ·
                refine ⟨2238792084984010076170807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2985056113312013434894409 2238792084984010076170807)
                ·
                  refine ⟨3358188127476015114256211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2238792084984010076170807 3358188127476015114256211)
                  ·
                    refine ⟨5037282191214022671384317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3358188127476015114256211 5037282191214022671384317)
                    ·
                      refine ⟨1888980821705258501769119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5037282191214022671384317 1888980821705258501769119)
                      ·
                        rfl

theorem cell23_3678777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_3678777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678777 prefixEnd_3678777 := by exact prefixLift 3678777
  have htrace : WordTrace (prefixWord ++ tailWord_3678777) baseStart_3678777 baseEnd_3678777 := by
    simpa [prefixWord, tailWord_3678777, baseEnd_3678777] using wordTrace_append hprefix tailTrace_3678777
  have hstable : (prefixWord ++ tailWord_3678777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678777).length < 2 ^ (prefixWord ++ tailWord_3678777).sum := by decide
  have hdescent : baseEnd_3678777 < baseStart_3678777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678789 : List Nat := [1, 3, 1, 1, 1, 5, 1, 10]
def baseStart_3678789 : Nat := 118140960795 + 3678789 * 2 ^ 59
def prefixEnd_3678789 : Nat := 4983230072969 + 3 ^ 40 * 3678789 * 2
def baseEnd_3678789 : Nat := 69962480869374535363669

theorem tailTrace_3678789 : CollatzResearch.WordTrace tailWord_3678789 prefixEnd_3678789 69962480869374535363669 := by
  unfold tailWord_3678789
  simp only [CollatzResearch.WordTrace]
  refine ⟨134176457869383214985815421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89450971912922143323876947 134176457869383214985815421)
  ·
    refine ⟨50316171701018705619680783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134176457869383214985815421 50316171701018705619680783)
    ·
      refine ⟨75474257551528058429521175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50316171701018705619680783 75474257551528058429521175)
      ·
        refine ⟨113211386327292087644281763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75474257551528058429521175 113211386327292087644281763)
        ·
          refine ⟨169817079490938131466422645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113211386327292087644281763 169817079490938131466422645)
          ·
            refine ⟨15920351202275449824977123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169817079490938131466422645 15920351202275449824977123)
            ·
              refine ⟨23880526803413174737465685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15920351202275449824977123 23880526803413174737465685)
              ·
                refine ⟨69962480869374535363669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23880526803413174737465685 69962480869374535363669)
                ·
                  rfl

theorem cell23_3678789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 10].length) (baseStart_3678789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678789 prefixEnd_3678789 := by exact prefixLift 3678789
  have htrace : WordTrace (prefixWord ++ tailWord_3678789) baseStart_3678789 baseEnd_3678789 := by
    simpa [prefixWord, tailWord_3678789, baseEnd_3678789] using wordTrace_append hprefix tailTrace_3678789
  have hstable : (prefixWord ++ tailWord_3678789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678789).length < 2 ^ (prefixWord ++ tailWord_3678789).sum := by decide
  have hdescent : baseEnd_3678789 < baseStart_3678789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678796 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 1, 2, 4]
def baseStart_3678796 : Nat := 118140960795 + 3678796 * 2 ^ 59
def prefixEnd_3678796 : Nat := 4983230072969 + 3 ^ 40 * 3678796 * 2
def baseEnd_3678796 : Nat := 1888990577837693927431531

theorem tailTrace_3678796 : CollatzResearch.WordTrace tailWord_3678796 prefixEnd_3678796 1888990577837693927431531 := by
  unfold tailWord_3678796
  simp only [CollatzResearch.WordTrace]
  refine ⟨67088356590178927590660121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89451142120238570120880161 67088356590178927590660121)
  ·
    refine ⟨50316267442634195692995091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67088356590178927590660121 50316267442634195692995091)
    ·
      refine ⟨75474401163951293539492637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50316267442634195692995091 75474401163951293539492637)
      ·
        refine ⟨28302900436481735077309739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75474401163951293539492637 28302900436481735077309739)
        ·
          refine ⟨42454350654722602615964609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28302900436481735077309739 42454350654722602615964609)
          ·
            refine ⟨31840762991041951961973457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42454350654722602615964609 31840762991041951961973457)
            ·
              refine ⟨23880572243281463971480093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31840762991041951961973457 23880572243281463971480093)
              ·
                refine ⟨8955214591230548989305035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23880572243281463971480093 8955214591230548989305035)
                ·
                  refine ⟨13432821886845823483957553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8955214591230548989305035 13432821886845823483957553)
                  ·
                    refine ⟨10074616415134367612968165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13432821886845823483957553 10074616415134367612968165)
                    ·
                      refine ⟨1888990577837693927431531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10074616415134367612968165 1888990577837693927431531)
                      ·
                        rfl

theorem cell23_3678796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_3678796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678796 prefixEnd_3678796 := by exact prefixLift 3678796
  have htrace : WordTrace (prefixWord ++ tailWord_3678796) baseStart_3678796 baseEnd_3678796 := by
    simpa [prefixWord, tailWord_3678796, baseEnd_3678796] using wordTrace_append hprefix tailTrace_3678796
  have hstable : (prefixWord ++ tailWord_3678796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678796).length < 2 ^ (prefixWord ++ tailWord_3678796).sum := by decide
  have hdescent : baseEnd_3678796 < baseStart_3678796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678816 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 3]
def baseStart_3678816 : Nat := 118140960795 + 3678816 * 2 ^ 59
def prefixEnd_3678816 : Nat := 4983230072969 + 3 ^ 40 * 3678816 * 2
def baseEnd_3678816 : Nat := 1889000847450783849181439

theorem tailTrace_3678816 : CollatzResearch.WordTrace tailWord_3678816 prefixEnd_3678816 1889000847450783849181439 := by
  unfold tailWord_3678816
  simp only [CollatzResearch.WordTrace]
  refine ⟨67088721320142699298524151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89451628426856932398032201 67088721320142699298524151)
  ·
    refine ⟨100633081980214048947786227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67088721320142699298524151 100633081980214048947786227)
    ·
      refine ⟨150949622970321073421679341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100633081980214048947786227 150949622970321073421679341)
      ·
        refine ⟨56606108613870402533129753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150949622970321073421679341 56606108613870402533129753)
        ·
          refine ⟨42454581460402801899847315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56606108613870402533129753 42454581460402801899847315)
          ·
            refine ⟨63681872190604202849770973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42454581460402801899847315 63681872190604202849770973)
            ·
              refine ⟨23880702071476576068664115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63681872190604202849770973 23880702071476576068664115)
              ·
                refine ⟨35821053107214864102996173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23880702071476576068664115 35821053107214864102996173)
                ·
                  refine ⟨13432894915205574038623565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35821053107214864102996173 13432894915205574038623565)
                  ·
                    refine ⟨5037335593202090264483837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13432894915205574038623565 5037335593202090264483837)
                    ·
                      refine ⟨1889000847450783849181439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5037335593202090264483837 1889000847450783849181439)
                      ·
                        rfl

theorem cell23_3678816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_3678816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678816 prefixEnd_3678816 := by exact prefixLift 3678816
  have htrace : WordTrace (prefixWord ++ tailWord_3678816) baseStart_3678816 baseEnd_3678816 := by
    simpa [prefixWord, tailWord_3678816, baseEnd_3678816] using wordTrace_append hprefix tailTrace_3678816
  have hstable : (prefixWord ++ tailWord_3678816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678816).length < 2 ^ (prefixWord ++ tailWord_3678816).sum := by decide
  have hdescent : baseEnd_3678816 < baseStart_3678816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678820 : List Nat := [2, 3, 1, 1, 2, 2, 5, 1, 1, 2, 3]
def baseStart_3678820 : Nat := 118140960795 + 3678820 * 2 ^ 59
def prefixEnd_3678820 : Nat := 4983230072969 + 3 ^ 40 * 3678820 * 2
def baseEnd_3678820 : Nat := 1889002901373401833531421

theorem tailTrace_3678820 : CollatzResearch.WordTrace tailWord_3678820 prefixEnd_3678820 1889002901373401833531421 := by
  unfold tailWord_3678820
  simp only [CollatzResearch.WordTrace]
  refine ⟨67088794266135453640096957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89451725688180604853462609 67088794266135453640096957)
  ·
    refine ⟨25158297849800795115036359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67088794266135453640096957 25158297849800795115036359)
    ·
      refine ⟨37737446774701192672554539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25158297849800795115036359 37737446774701192672554539)
      ·
        refine ⟨56606170162051789008831809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37737446774701192672554539 56606170162051789008831809)
        ·
          refine ⟨42454627621538841756623857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56606170162051789008831809 42454627621538841756623857)
          ·
            refine ⟨31840970716154131317467893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42454627621538841756623857 31840970716154131317467893)
            ·
              refine ⟨2985091004639449811012615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31840970716154131317467893 2985091004639449811012615)
              ·
                refine ⟨4477636506959174716518923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2985091004639449811012615 4477636506959174716518923)
                ·
                  refine ⟨6716454760438762074778385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4477636506959174716518923 6716454760438762074778385)
                  ·
                    refine ⟨5037341070329071556083789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6716454760438762074778385 5037341070329071556083789)
                    ·
                      refine ⟨1889002901373401833531421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5037341070329071556083789 1889002901373401833531421)
                      ·
                        rfl

theorem cell23_3678820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_3678820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678820 prefixEnd_3678820 := by exact prefixLift 3678820
  have htrace : WordTrace (prefixWord ++ tailWord_3678820) baseStart_3678820 baseEnd_3678820 := by
    simpa [prefixWord, tailWord_3678820, baseEnd_3678820] using wordTrace_append hprefix tailTrace_3678820
  have hstable : (prefixWord ++ tailWord_3678820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678820).length < 2 ^ (prefixWord ++ tailWord_3678820).sum := by decide
  have hdescent : baseEnd_3678820 < baseStart_3678820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678834 : List Nat := [3, 2, 1, 2, 4, 1, 1, 4, 1, 2, 2]
def baseStart_3678834 : Nat := 118140960795 + 3678834 * 2 ^ 59
def prefixEnd_3678834 : Nat := 4983230072969 + 3 ^ 40 * 3678834 * 2
def baseEnd_3678834 : Nat := 1889010090102564778756357

theorem tailTrace_3678834 : CollatzResearch.WordTrace tailWord_3678834 prefixEnd_3678834 1889010090102564778756357 := by
  unfold tailWord_3678834
  simp only [CollatzResearch.WordTrace]
  refine ⟨33544524788555046917800889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89452066102813458447469037 33544524788555046917800889)
  ·
    refine ⟨25158393591416285188350667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33544524788555046917800889 25158393591416285188350667)
    ·
      refine ⟨37737590387124427782526001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25158393591416285188350667 37737590387124427782526001)
      ·
        refine ⟨28303192790343320836894501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37737590387124427782526001 28303192790343320836894501)
        ·
          refine ⟨5306848648189372656917719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28303192790343320836894501 5306848648189372656917719)
          ·
            refine ⟨7960272972284058985376579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306848648189372656917719 7960272972284058985376579)
            ·
              refine ⟨11940409458426088478064869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7960272972284058985376579 11940409458426088478064869)
              ·
                refine ⟨2238826773454891589637163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11940409458426088478064869 2238826773454891589637163)
                ·
                  refine ⟨3358240160182337384455745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2238826773454891589637163 3358240160182337384455745)
                  ·
                    refine ⟨2518680120136753038341809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3358240160182337384455745 2518680120136753038341809)
                    ·
                      refine ⟨1889010090102564778756357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518680120136753038341809 1889010090102564778756357)
                      ·
                        rfl

theorem cell23_3678834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_3678834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678834 prefixEnd_3678834 := by exact prefixLift 3678834
  have htrace : WordTrace (prefixWord ++ tailWord_3678834) baseStart_3678834 baseEnd_3678834 := by
    simpa [prefixWord, tailWord_3678834, baseEnd_3678834] using wordTrace_append hprefix tailTrace_3678834
  have hstable : (prefixWord ++ tailWord_3678834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678834).length < 2 ^ (prefixWord ++ tailWord_3678834).sum := by decide
  have hdescent : baseEnd_3678834 < baseStart_3678834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678873 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 1, 4, 2]
def baseStart_3678873 : Nat := 118140960795 + 3678873 * 2 ^ 59
def prefixEnd_3678873 : Nat := 4983230072969 + 3 ^ 40 * 3678873 * 2
def baseEnd_3678873 : Nat := 1889030115848090126168677

theorem tailTrace_3678873 : CollatzResearch.WordTrace tailWord_3678873 prefixEnd_3678873 1889030115848090126168677 := by
  unfold tailWord_3678873
  simp only [CollatzResearch.WordTrace]
  refine ⟨134179521601078897331873273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89453014400719264887915515 134179521601078897331873273)
  ·
    refine ⟨100634641200809172998904955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134179521601078897331873273 100634641200809172998904955)
    ·
      refine ⟨150951961801213759498357433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100634641200809172998904955 150951961801213759498357433)
      ·
        refine ⟨113213971350910319623768075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150951961801213759498357433 113213971350910319623768075)
        ·
          refine ⟨169820957026365479435652113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113213971350910319623768075 169820957026365479435652113)
          ·
            refine ⟨127365717769774109576739085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169820957026365479435652113 127365717769774109576739085)
            ·
              refine ⟨47762144163665291091277157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127365717769774109576739085 47762144163665291091277157)
              ·
                refine ⟨8955402030687242079614467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47762144163665291091277157 8955402030687242079614467)
                ·
                  refine ⟨13433103046030863119421701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8955402030687242079614467 13433103046030863119421701)
                  ·
                    refine ⟨2518706821130786834891569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13433103046030863119421701 2518706821130786834891569)
                    ·
                      refine ⟨1889030115848090126168677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518706821130786834891569 1889030115848090126168677)
                      ·
                        rfl

theorem cell23_3678873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 4, 2].length) (baseStart_3678873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678873 prefixEnd_3678873 := by exact prefixLift 3678873
  have htrace : WordTrace (prefixWord ++ tailWord_3678873) baseStart_3678873 baseEnd_3678873 := by
    simpa [prefixWord, tailWord_3678873, baseEnd_3678873] using wordTrace_append hprefix tailTrace_3678873
  have hstable : (prefixWord ++ tailWord_3678873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678873).length < 2 ^ (prefixWord ++ tailWord_3678873).sum := by decide
  have hdescent : baseEnd_3678873 < baseStart_3678873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678877 : List Nat := [1, 4, 2, 1, 1, 1, 6, 1, 1, 3, 2]
def baseStart_3678877 : Nat := 118140960795 + 3678877 * 2 ^ 59
def prefixEnd_3678877 : Nat := 4983230072969 + 3 ^ 40 * 3678877 * 2
def baseEnd_3678877 : Nat := 1889032169770708110518659

theorem tailTrace_3678877 : CollatzResearch.WordTrace tailWord_3678877 prefixEnd_3678877 1889032169770708110518659 := by
  unfold tailWord_3678877
  simp only [CollatzResearch.WordTrace]
  refine ⟨134179667493064406015018885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89453111662042937343345923 134179667493064406015018885)
  ·
    refine ⟨25158687654949576127816041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134179667493064406015018885 25158687654949576127816041)
    ·
      refine ⟨18869015741212182095862031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25158687654949576127816041 18869015741212182095862031)
      ·
        refine ⟨28303523611818273143793047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18869015741212182095862031 28303523611818273143793047)
        ·
          refine ⟨42455285417727409715689571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28303523611818273143793047 42455285417727409715689571)
          ·
            refine ⟨63682928126591114573534357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42455285417727409715689571 63682928126591114573534357)
            ·
              refine ⟨2985137255933958495634423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63682928126591114573534357 2985137255933958495634423)
              ·
                refine ⟨4477705883900937743451635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2985137255933958495634423 4477705883900937743451635)
                ·
                  refine ⟨6716558825851406615177453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4477705883900937743451635 6716558825851406615177453)
                  ·
                    refine ⟨2518709559694277480691545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6716558825851406615177453 2518709559694277480691545)
                    ·
                      refine ⟨1889032169770708110518659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518709559694277480691545 1889032169770708110518659)
                      ·
                        rfl

theorem cell23_3678877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_3678877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678877 prefixEnd_3678877 := by exact prefixLift 3678877
  have htrace : WordTrace (prefixWord ++ tailWord_3678877) baseStart_3678877 baseEnd_3678877 := by
    simpa [prefixWord, tailWord_3678877, baseEnd_3678877] using wordTrace_append hprefix tailTrace_3678877
  have hstable : (prefixWord ++ tailWord_3678877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678877).length < 2 ^ (prefixWord ++ tailWord_3678877).sum := by decide
  have hdescent : baseEnd_3678877 < baseStart_3678877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678943 : List Nat := [1, 1, 2, 3, 2, 4, 1, 2, 2, 5]
def baseStart_3678943 : Nat := 118140960795 + 3678943 * 2 ^ 59
def prefixEnd_3678943 : Nat := 4983230072969 + 3 ^ 40 * 3678943 * 2
def baseEnd_3678943 : Nat := 629688686497968284097785

theorem tailTrace_3678943 : CollatzResearch.WordTrace tailWord_3678943 prefixEnd_3678943 629688686497968284097785 := by
  unfold tailWord_3678943
  simp only [CollatzResearch.WordTrace]
  refine ⟨134182074710825299286921483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89454716473883532857947655 134182074710825299286921483)
  ·
    refine ⟨201273112066237948930382225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134182074710825299286921483 201273112066237948930382225)
    ·
      refine ⟨150954834049678461697786669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201273112066237948930382225 150954834049678461697786669)
      ·
        refine ⟨56608062768629423136670001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150954834049678461697786669 56608062768629423136670001)
        ·
          refine ⟨42456047076472067352502501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56608062768629423136670001 42456047076472067352502501)
          ·
            refine ⟨7960508826838512628594219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42456047076472067352502501 7960508826838512628594219)
            ·
              refine ⟨11940763240257768942891329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7960508826838512628594219 11940763240257768942891329)
              ·
                refine ⟨8955572430193326707168497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11940763240257768942891329 8955572430193326707168497)
                ·
                  refine ⟨6716679322644995030376373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8955572430193326707168497 6716679322644995030376373)
                  ·
                    refine ⟨629688686497968284097785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6716679322644995030376373 629688686497968284097785)
                    ·
                      rfl

theorem cell23_3678943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 5].length) (baseStart_3678943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678943 prefixEnd_3678943 := by exact prefixLift 3678943
  have htrace : WordTrace (prefixWord ++ tailWord_3678943) baseStart_3678943 baseEnd_3678943 := by
    simpa [prefixWord, tailWord_3678943, baseEnd_3678943] using wordTrace_append hprefix tailTrace_3678943
  have hstable : (prefixWord ++ tailWord_3678943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678943).length < 2 ^ (prefixWord ++ tailWord_3678943).sum := by decide
  have hdescent : baseEnd_3678943 < baseStart_3678943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678947 : List Nat := [1, 1, 1, 7, 1, 2, 3, 2, 5]
def baseStart_3678947 : Nat := 118140960795 + 3678947 * 2 ^ 59
def prefixEnd_3678947 : Nat := 4983230072969 + 3 ^ 40 * 3678947 * 2
def baseEnd_3678947 : Nat := 209896457046280315182593

theorem tailTrace_3678947 : CollatzResearch.WordTrace tailWord_3678947 prefixEnd_3678947 209896457046280315182593 := by
  unfold tailWord_3678947
  simp only [CollatzResearch.WordTrace]
  refine ⟨134182220602810807970067095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89454813735207205313378063 134182220602810807970067095)
  ·
    refine ⟨201273330904216211955100643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134182220602810807970067095 201273330904216211955100643)
    ·
      refine ⟨301909996356324317932650965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201273330904216211955100643 301909996356324317932650965)
      ·
        refine ⟨7076015539601351201546507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 301909996356324317932650965 7076015539601351201546507)
        ·
          refine ⟨10614023309402026802319761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7076015539601351201546507 10614023309402026802319761)
          ·
            refine ⟨7960517482051520101739821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10614023309402026802319761 7960517482051520101739821)
            ·
              refine ⟨2985194055769320038152433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7960517482051520101739821 2985194055769320038152433)
              ·
                refine ⟨2238895541826990028614325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2985194055769320038152433 2238895541826990028614325)
                ·
                  refine ⟨209896457046280315182593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2238895541826990028614325 209896457046280315182593)
                  ·
                    rfl

theorem cell23_3678947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 3, 2, 5].length) (baseStart_3678947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678947 prefixEnd_3678947 := by exact prefixLift 3678947
  have htrace : WordTrace (prefixWord ++ tailWord_3678947) baseStart_3678947 baseEnd_3678947 := by
    simpa [prefixWord, tailWord_3678947, baseEnd_3678947] using wordTrace_append hprefix tailTrace_3678947
  have hstable : (prefixWord ++ tailWord_3678947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678947).length < 2 ^ (prefixWord ++ tailWord_3678947).sum := by decide
  have hdescent : baseEnd_3678947 < baseStart_3678947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678963 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 1, 6, 2]
def baseStart_3678963 : Nat := 118140960795 + 3678963 * 2 ^ 59
def prefixEnd_3678963 : Nat := 4983230072969 + 3 ^ 40 * 3678963 * 2
def baseEnd_3678963 : Nat := 1889076329106994774043263

theorem tailTrace_3678963 : CollatzResearch.WordTrace tailWord_3678963 prefixEnd_3678963 1889076329106994774043263 := by
  unfold tailWord_3678963
  simp only [CollatzResearch.WordTrace]
  refine ⟨134182804170752842702649543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89455202780501895135099695 134182804170752842702649543)
  ·
    refine ⟨201274206256129264053974315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134182804170752842702649543 201274206256129264053974315)
    ·
      refine ⟨301911309384193896080961473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201274206256129264053974315 301911309384193896080961473)
      ·
        refine ⟨226433482038145422060721105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301911309384193896080961473 226433482038145422060721105)
        ·
          refine ⟨169825111528609066545540829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226433482038145422060721105 169825111528609066545540829)
          ·
            refine ⟨63684416823228399954577811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169825111528609066545540829 63684416823228399954577811)
            ·
              refine ⟨95526625234842599931866717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63684416823228399954577811 95526625234842599931866717)
              ·
                refine ⟨35822484463065974974450019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95526625234842599931866717 35822484463065974974450019)
                ·
                  refine ⟨53733726694598962461675029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35822484463065974974450019 53733726694598962461675029)
                  ·
                    refine ⟨2518768438809326365391017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53733726694598962461675029 2518768438809326365391017)
                    ·
                      refine ⟨1889076329106994774043263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518768438809326365391017 1889076329106994774043263)
                      ·
                        rfl

theorem cell23_3678963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 6, 2].length) (baseStart_3678963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678963 prefixEnd_3678963 := by exact prefixLift 3678963
  have htrace : WordTrace (prefixWord ++ tailWord_3678963) baseStart_3678963 baseEnd_3678963 := by
    simpa [prefixWord, tailWord_3678963, baseEnd_3678963] using wordTrace_append hprefix tailTrace_3678963
  have hstable : (prefixWord ++ tailWord_3678963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678963).length < 2 ^ (prefixWord ++ tailWord_3678963).sum := by decide
  have hdescent : baseEnd_3678963 < baseStart_3678963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678973 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 5, 4]
def baseStart_3678973 : Nat := 118140960795 + 3678973 * 2 ^ 59
def prefixEnd_3678973 : Nat := 4983230072969 + 3 ^ 40 * 3678973 * 2
def baseEnd_3678973 : Nat := 629693821304513244972739

theorem tailTrace_3678973 : CollatzResearch.WordTrace tailWord_3678973 prefixEnd_3678973 629693821304513244972739 := by
  unfold tailWord_3678973
  simp only [CollatzResearch.WordTrace]
  refine ⟨134183168900716614410513573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89455445933811076273675715 134183168900716614410513573)
  ·
    refine ⟨25159344168884365201971295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134183168900716614410513573 25159344168884365201971295)
    ·
      refine ⟨37739016253326547802956943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25159344168884365201971295 37739016253326547802956943)
      ·
        refine ⟨56608524379989821704435415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37739016253326547802956943 56608524379989821704435415)
        ·
          refine ⟨84912786569984732556653123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56608524379989821704435415 84912786569984732556653123)
          ·
            refine ⟨127369179854977098834979685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84912786569984732556653123 127369179854977098834979685)
            ·
              refine ⟨23881721222808206031558691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127369179854977098834979685 23881721222808206031558691)
              ·
                refine ⟨35822581834212309047338037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23881721222808206031558691 35822581834212309047338037)
                ·
                  refine ⟨3358367046957403973187941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35822581834212309047338037 3358367046957403973187941)
                  ·
                    refine ⟨629693821304513244972739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3358367046957403973187941 629693821304513244972739)
                    ·
                      rfl

theorem cell23_3678973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_3678973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678973 prefixEnd_3678973 := by exact prefixLift 3678973
  have htrace : WordTrace (prefixWord ++ tailWord_3678973) baseStart_3678973 baseEnd_3678973 := by
    simpa [prefixWord, tailWord_3678973, baseEnd_3678973] using wordTrace_append hprefix tailTrace_3678973
  have hstable : (prefixWord ++ tailWord_3678973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678973).length < 2 ^ (prefixWord ++ tailWord_3678973).sum := by decide
  have hdescent : baseEnd_3678973 < baseStart_3678973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3678980 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_3678980 : Nat := 118140960795 + 3678980 * 2 ^ 59
def prefixEnd_3678980 : Nat := 4983230072969 + 3 ^ 40 * 3678980 * 2
def baseEnd_3678980 : Nat := 1889085058278121207530685

theorem tailTrace_3678980 : CollatzResearch.WordTrace tailWord_3678980 prefixEnd_3678980 1889085058278121207530685 := by
  unfold tailWord_3678980
  simp only [CollatzResearch.WordTrace]
  refine ⟨67091712105845627303009197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89455616141127503070678929 67091712105845627303009197)
  ·
    refine ⟨25159392039692110238628449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67091712105845627303009197 25159392039692110238628449)
    ·
      refine ⟨18869544029769082678971337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25159392039692110238628449 18869544029769082678971337)
      ·
        refine ⟨14152158022326812009228503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18869544029769082678971337 14152158022326812009228503)
        ·
          refine ⟨21228237033490218013842755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14152158022326812009228503 21228237033490218013842755)
          ·
            refine ⟨31842355550235327020764133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21228237033490218013842755 31842355550235327020764133)
            ·
              refine ⟨5970441665669123816393275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31842355550235327020764133 5970441665669123816393275)
              ·
                refine ⟨8955662498503685724589913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5970441665669123816393275 8955662498503685724589913)
                ·
                  refine ⟨6716746873877764293442435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8955662498503685724589913 6716746873877764293442435)
                  ·
                    refine ⟨10075120310816646440163653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6716746873877764293442435 10075120310816646440163653)
                    ·
                      refine ⟨1889085058278121207530685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10075120310816646440163653 1889085058278121207530685)
                      ·
                        rfl

theorem cell23_3678980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_3678980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3678980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3678980 prefixEnd_3678980 := by exact prefixLift 3678980
  have htrace : WordTrace (prefixWord ++ tailWord_3678980) baseStart_3678980 baseEnd_3678980 := by
    simpa [prefixWord, tailWord_3678980, baseEnd_3678980] using wordTrace_append hprefix tailTrace_3678980
  have hstable : (prefixWord ++ tailWord_3678980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3678980).length < 2 ^ (prefixWord ++ tailWord_3678980).sum := by decide
  have hdescent : baseEnd_3678980 < baseStart_3678980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3678980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679007 : List Nat := [1, 1, 2, 4, 2, 3, 1, 4, 1, 4]
def baseStart_3679007 : Nat := 118140960795 + 3679007 * 2 ^ 59
def prefixEnd_3679007 : Nat := 4983230072969 + 3 ^ 40 * 3679007 * 2
def baseEnd_3679007 : Nat := 629699640751930867297687

theorem tailTrace_3679007 : CollatzResearch.WordTrace tailWord_3679007 prefixEnd_3679007 629699640751930867297687 := by
  unfold tailWord_3679007
  simp only [CollatzResearch.WordTrace]
  refine ⟨134184408982593438217251275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89456272655062292144834183 134184408982593438217251275)
  ·
    refine ⟨201276613473890157325876913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134184408982593438217251275 201276613473890157325876913)
    ·
      refine ⟨150957460105417617994407685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201276613473890157325876913 150957460105417617994407685)
      ·
        refine ⟨28304523769765803373951441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150957460105417617994407685 28304523769765803373951441)
        ·
          refine ⟨21228392827324352530463581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28304523769765803373951441 21228392827324352530463581)
          ·
            refine ⟨7960647310246632198923843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21228392827324352530463581 7960647310246632198923843)
            ·
              refine ⟨11940970965369948298385765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7960647310246632198923843 11940970965369948298385765)
              ·
                refine ⟨2238932056006865305947331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11940970965369948298385765 2238932056006865305947331)
                ·
                  refine ⟨3358398084010297958920997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2238932056006865305947331 3358398084010297958920997)
                  ·
                    refine ⟨629699640751930867297687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3358398084010297958920997 629699640751930867297687)
                    ·
                      rfl

theorem cell23_3679007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 1, 4].length) (baseStart_3679007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679007 prefixEnd_3679007 := by exact prefixLift 3679007
  have htrace : WordTrace (prefixWord ++ tailWord_3679007) baseStart_3679007 baseEnd_3679007 := by
    simpa [prefixWord, tailWord_3679007, baseEnd_3679007] using wordTrace_append hprefix tailTrace_3679007
  have hstable : (prefixWord ++ tailWord_3679007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679007).length < 2 ^ (prefixWord ++ tailWord_3679007).sum := by decide
  have hdescent : baseEnd_3679007 < baseStart_3679007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679034 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3]
def baseStart_3679034 : Nat := 118140960795 + 3679034 * 2 ^ 59
def prefixEnd_3679034 : Nat := 4983230072969 + 3 ^ 40 * 3679034 * 2
def baseEnd_3679034 : Nat := 1889112786233463996255437

theorem tailTrace_3679034 : CollatzResearch.WordTrace tailWord_3679034 prefixEnd_3679034 1889112786233463996255437 := by
  unfold tailWord_3679034
  simp only [CollatzResearch.WordTrace]
  refine ⟨33546348438373905457121039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89456929168997081218989437 33546348438373905457121039)
  ·
    refine ⟨50319522657560858185681559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33546348438373905457121039 50319522657560858185681559)
    ·
      refine ⟨75479283986341287278522339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50319522657560858185681559 75479283986341287278522339)
      ·
        refine ⟨113218925979511930917783509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75479283986341287278522339 113218925979511930917783509)
        ·
          refine ⟨2653568577644810880885551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 113218925979511930917783509 2653568577644810880885551)
          ·
            refine ⟨3980352866467216321328327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2653568577644810880885551 3980352866467216321328327)
            ·
              refine ⟨5970529299700824481992491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3980352866467216321328327 5970529299700824481992491)
              ·
                refine ⟨8955793949551236722988737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5970529299700824481992491 8955793949551236722988737)
                ·
                  refine ⟨6716845462163427542241553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8955793949551236722988737 6716845462163427542241553)
                  ·
                    refine ⟨5037634096622570656681165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6716845462163427542241553 5037634096622570656681165)
                    ·
                      refine ⟨1889112786233463996255437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5037634096622570656681165 1889112786233463996255437)
                      ·
                        rfl

theorem cell23_3679034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3].length) (baseStart_3679034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679034 prefixEnd_3679034 := by exact prefixLift 3679034
  have htrace : WordTrace (prefixWord ++ tailWord_3679034) baseStart_3679034 baseEnd_3679034 := by
    simpa [prefixWord, tailWord_3679034, baseEnd_3679034] using wordTrace_append hprefix tailTrace_3679034
  have hstable : (prefixWord ++ tailWord_3679034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679034).length < 2 ^ (prefixWord ++ tailWord_3679034).sum := by decide
  have hdescent : baseEnd_3679034 < baseStart_3679034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679041 : List Nat := [1, 2, 5, 3, 1, 1, 2, 3, 1, 4]
def baseStart_3679041 : Nat := 118140960795 + 3679041 * 2 ^ 59
def prefixEnd_3679041 : Nat := 4983230072969 + 3 ^ 40 * 3679041 * 2
def baseEnd_3679041 : Nat := 629705460199348489622635

theorem tailTrace_3679041 : CollatzResearch.WordTrace tailWord_3679041 prefixEnd_3679041 629705460199348489622635 := by
  unfold tailWord_3679041
  simp only [CollatzResearch.WordTrace]
  refine ⟨134185649064470262023988977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89457099376313508015992651 134185649064470262023988977)
  ·
    refine ⟨100639236798352696517991733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134185649064470262023988977 100639236798352696517991733)
    ·
      refine ⟨9434928449845565298561725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100639236798352696517991733 9434928449845565298561725)
      ·
        refine ⟨3538098168692086986960647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9434928449845565298561725 3538098168692086986960647)
        ·
          refine ⟨5307147253038130480440971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3538098168692086986960647 5307147253038130480440971)
          ·
            refine ⟨7960720879557195720661457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307147253038130480440971 7960720879557195720661457)
            ·
              refine ⟨5970540659667896790496093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7960720879557195720661457 5970540659667896790496093)
              ·
                refine ⟨2238952747375461296436035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5970540659667896790496093 2238952747375461296436035)
                ·
                  refine ⟨3358429121063191944654053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2238952747375461296436035 3358429121063191944654053)
                  ·
                    refine ⟨629705460199348489622635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3358429121063191944654053 629705460199348489622635)
                    ·
                      rfl

theorem cell23_3679041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_3679041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679041 prefixEnd_3679041 := by exact prefixLift 3679041
  have htrace : WordTrace (prefixWord ++ tailWord_3679041) baseStart_3679041 baseEnd_3679041 := by
    simpa [prefixWord, tailWord_3679041, baseEnd_3679041] using wordTrace_append hprefix tailTrace_3679041
  have hstable : (prefixWord ++ tailWord_3679041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679041).length < 2 ^ (prefixWord ++ tailWord_3679041).sum := by decide
  have hdescent : baseEnd_3679041 < baseStart_3679041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679073 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 2, 6, 3]
def baseStart_3679073 : Nat := 118140960795 + 3679073 * 2 ^ 59
def prefixEnd_3679073 : Nat := 4983230072969 + 3 ^ 40 * 3679073 * 2
def baseEnd_3679073 : Nat := 1889132811978989343667757

theorem tailTrace_3679073 : CollatzResearch.WordTrace tailWord_3679073 prefixEnd_3679073 1889132811978989343667757 := by
  unfold tailWord_3679073
  simp only [CollatzResearch.WordTrace]
  refine ⟨134186816200354331489153873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89457877466902887659435915 134186816200354331489153873)
  ·
    refine ⟨100640112150265748616865405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134186816200354331489153873 100640112150265748616865405)
    ·
      refine ⟨37740042056349655731324527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100640112150265748616865405 37740042056349655731324527)
      ·
        refine ⟨56610063084524483596986791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37740042056349655731324527 56610063084524483596986791)
        ·
          refine ⟨84915094626786725395480187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56610063084524483596986791 84915094626786725395480187)
          ·
            refine ⟨127372641940180088093220281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84915094626786725395480187 127372641940180088093220281)
            ·
              refine ⟨95529481455135066069915211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127372641940180088093220281 95529481455135066069915211)
              ·
                refine ⟨143294222182702599104872817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95529481455135066069915211 143294222182702599104872817)
                ·
                  refine ⟨107470666637026949328654613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143294222182702599104872817 107470666637026949328654613)
                  ·
                    refine ⟨5037687498610638249780685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107470666637026949328654613 5037687498610638249780685)
                    ·
                      refine ⟨1889132811978989343667757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5037687498610638249780685 1889132811978989343667757)
                      ·
                        rfl

theorem cell23_3679073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_3679073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679073 prefixEnd_3679073 := by exact prefixLift 3679073
  have htrace : WordTrace (prefixWord ++ tailWord_3679073) baseStart_3679073 baseEnd_3679073 := by
    simpa [prefixWord, tailWord_3679073, baseEnd_3679073] using wordTrace_append hprefix tailTrace_3679073
  have hstable : (prefixWord ++ tailWord_3679073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679073).length < 2 ^ (prefixWord ++ tailWord_3679073).sum := by decide
  have hdescent : baseEnd_3679073 < baseStart_3679073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679080 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 1, 6]
def baseStart_3679080 : Nat := 118140960795 + 3679080 * 2 ^ 59
def prefixEnd_3679080 : Nat := 4983230072969 + 3 ^ 40 * 3679080 * 2
def baseEnd_3679080 : Nat := 629712135447856938760075

theorem tailTrace_3679080 : CollatzResearch.WordTrace tailWord_3679080 prefixEnd_3679080 629712135447856938760075 := by
  unfold tailWord_3679080
  simp only [CollatzResearch.WordTrace]
  refine ⟨67093535755664485842329347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89458047674219314456439129 67093535755664485842329347)
  ·
    refine ⟨100640303633496728763494021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67093535755664485842329347 100640303633496728763494021)
    ·
      refine ⟨18870056931280636643155129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100640303633496728763494021 18870056931280636643155129)
      ·
        refine ⟨14152542698460477482366347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18870056931280636643155129 14152542698460477482366347)
        ·
          refine ⟨21228814047690716223549521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14152542698460477482366347 21228814047690716223549521)
          ·
            refine ⟨15921610535768037167662141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21228814047690716223549521 15921610535768037167662141)
            ·
              refine ⟨5970603950913013937873303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15921610535768037167662141 5970603950913013937873303)
              ·
                refine ⟨8955905926369520906809955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5970603950913013937873303 8955905926369520906809955)
                ·
                  refine ⟨13433858889554281360214933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8955905926369520906809955 13433858889554281360214933)
                  ·
                    refine ⟨629712135447856938760075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13433858889554281360214933 629712135447856938760075)
                    ·
                      rfl

theorem cell23_3679080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_3679080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679080 prefixEnd_3679080 := by exact prefixLift 3679080
  have htrace : WordTrace (prefixWord ++ tailWord_3679080) baseStart_3679080 baseEnd_3679080 := by
    simpa [prefixWord, tailWord_3679080, baseEnd_3679080] using wordTrace_append hprefix tailTrace_3679080
  have hstable : (prefixWord ++ tailWord_3679080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679080).length < 2 ^ (prefixWord ++ tailWord_3679080).sum := by decide
  have hdescent : baseEnd_3679080 < baseStart_3679080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679090 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 3, 2, 3]
def baseStart_3679090 : Nat := 118140960795 + 3679090 * 2 ^ 59
def prefixEnd_3679090 : Nat := 4983230072969 + 3 ^ 40 * 3679090 * 2
def baseEnd_3679090 : Nat := 1889141541150115777155179

theorem tailTrace_3679090 : CollatzResearch.WordTrace tailWord_3679090 prefixEnd_3679090 1889141541150115777155179 := by
  unfold tailWord_3679090
  simp only [CollatzResearch.WordTrace]
  refine ⟨33546859060323185848130681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89458290827528495595015149 33546859060323185848130681)
  ·
    refine ⟨25160144295242389386098011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33546859060323185848130681 25160144295242389386098011)
    ·
      refine ⟨37740216442863584079147017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25160144295242389386098011 37740216442863584079147017)
      ·
        refine ⟨28305162332147688059360263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37740216442863584079147017 28305162332147688059360263)
        ·
          refine ⟨42457743498221532089040395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28305162332147688059360263 42457743498221532089040395)
          ·
            refine ⟨63686615247332298133560593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42457743498221532089040395 63686615247332298133560593)
            ·
              refine ⟨47764961435499223600170445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63686615247332298133560593 47764961435499223600170445)
              ·
                refine ⟨17911860538312208850063917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47764961435499223600170445 17911860538312208850063917)
                ·
                  refine ⟨6716947701867078318773969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17911860538312208850063917 6716947701867078318773969)
                  ·
                    refine ⟨5037710776400308739080477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6716947701867078318773969 5037710776400308739080477)
                    ·
                      refine ⟨1889141541150115777155179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5037710776400308739080477 1889141541150115777155179)
                      ·
                        rfl

theorem cell23_3679090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_3679090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679090 prefixEnd_3679090 := by exact prefixLift 3679090
  have htrace : WordTrace (prefixWord ++ tailWord_3679090) baseStart_3679090 baseEnd_3679090 := by
    simpa [prefixWord, tailWord_3679090, baseEnd_3679090] using wordTrace_append hprefix tailTrace_3679090
  have hstable : (prefixWord ++ tailWord_3679090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679090).length < 2 ^ (prefixWord ++ tailWord_3679090).sum := by decide
  have hdescent : baseEnd_3679090 < baseStart_3679090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679104 : List Nat := [2, 1, 1, 2, 1, 2, 2, 7, 1, 2, 2]
def baseStart_3679104 : Nat := 118140960795 + 3679104 * 2 ^ 59
def prefixEnd_3679104 : Nat := 4983230072969 + 3 ^ 40 * 3679104 * 2
def baseEnd_3679104 : Nat := 1889148729879278722380115

theorem tailTrace_3679104 : CollatzResearch.WordTrace tailWord_3679104 prefixEnd_3679104 1889148729879278722380115 := by
  unfold tailWord_3679104
  simp only [CollatzResearch.WordTrace]
  refine ⟨67093973431621011891766183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89458631242161349189021577 67093973431621011891766183)
  ·
    refine ⟨100640960147431517837649275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67093973431621011891766183 100640960147431517837649275)
    ·
      refine ⟨150961440221147276756473913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100640960147431517837649275 150961440221147276756473913)
      ·
        refine ⟨113221080165860457567355435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150961440221147276756473913 113221080165860457567355435)
        ·
          refine ⟨169831620248790686351033153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113221080165860457567355435 169831620248790686351033153)
          ·
            refine ⟨127373715186593014763274865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169831620248790686351033153 127373715186593014763274865)
            ·
              refine ⟨95530286389944761072456149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127373715186593014763274865 95530286389944761072456149)
              ·
                refine ⟨2238991087264330337635691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95530286389944761072456149 2238991087264330337635691)
                ·
                  refine ⟨3358486630896495506453537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2238991087264330337635691 3358486630896495506453537)
                  ·
                    refine ⟨2518864973172371629840153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3358486630896495506453537 2518864973172371629840153)
                    ·
                      refine ⟨1889148729879278722380115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518864973172371629840153 1889148729879278722380115)
                      ·
                        rfl

theorem cell23_3679104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 7, 1, 2, 2].length) (baseStart_3679104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679104 prefixEnd_3679104 := by exact prefixLift 3679104
  have htrace : WordTrace (prefixWord ++ tailWord_3679104) baseStart_3679104 baseEnd_3679104 := by
    simpa [prefixWord, tailWord_3679104, baseEnd_3679104] using wordTrace_append hprefix tailTrace_3679104
  have hstable : (prefixWord ++ tailWord_3679104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679104).length < 2 ^ (prefixWord ++ tailWord_3679104).sum := by decide
  have hdescent : baseEnd_3679104 < baseStart_3679104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679120 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 8, 1, 3]
def baseStart_3679120 : Nat := 118140960795 + 3679120 * 2 ^ 59
def prefixEnd_3679120 : Nat := 4983230072969 + 3 ^ 40 * 3679120 * 2
def baseEnd_3679120 : Nat := 1889156945569750659780041

theorem tailTrace_3679120 : CollatzResearch.WordTrace tailWord_3679120 prefixEnd_3679120 1889156945569750659780041 := by
  unfold tailWord_3679120
  simp only [CollatzResearch.WordTrace]
  refine ⟨67094265215592029258057407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89459020287456039010743209 67094265215592029258057407)
  ·
    refine ⟨100641397823388043887086111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67094265215592029258057407 100641397823388043887086111)
    ·
      refine ⟨150962096735082065830629167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100641397823388043887086111 150962096735082065830629167)
      ·
        refine ⟨226443145102623098745943751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150962096735082065830629167 226443145102623098745943751)
        ·
          refine ⟨339664717653934648118915627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226443145102623098745943751 339664717653934648118915627)
          ·
            refine ⟨509497076480901972178373441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339664717653934648118915627 509497076480901972178373441)
            ·
              refine ⟨382122807360676479133780081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509497076480901972178373441 382122807360676479133780081)
              ·
                refine ⟨286592105520507359350335061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382122807360676479133780081 286592105520507359350335061)
                ·
                  refine ⟨3358501236568445617386739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 286592105520507359350335061 3358501236568445617386739)
                  ·
                    refine ⟨5037751854852668426080109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3358501236568445617386739 5037751854852668426080109)
                    ·
                      refine ⟨1889156945569750659780041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5037751854852668426080109 1889156945569750659780041)
                      ·
                        rfl

theorem cell23_3679120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 8, 1, 3].length) (baseStart_3679120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679120 prefixEnd_3679120 := by exact prefixLift 3679120
  have htrace : WordTrace (prefixWord ++ tailWord_3679120) baseStart_3679120 baseEnd_3679120 := by
    simpa [prefixWord, tailWord_3679120, baseEnd_3679120] using wordTrace_append hprefix tailTrace_3679120
  have hstable : (prefixWord ++ tailWord_3679120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679120).length < 2 ^ (prefixWord ++ tailWord_3679120).sum := by decide
  have hdescent : baseEnd_3679120 < baseStart_3679120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679158 : List Nat := [5, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3679158 : Nat := 118140960795 + 3679158 * 2 ^ 59
def prefixEnd_3679158 : Nat := 4983230072969 + 3 ^ 40 * 3679158 * 2
def baseEnd_3679158 : Nat := 1889176457834621511104867

theorem tailTrace_3679158 : CollatzResearch.WordTrace tailWord_3679158 prefixEnd_3679158 1889176457834621511104867 := by
  unfold tailWord_3679158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8386869775315399437874883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89459944270030927337332085 8386869775315399437874883)
  ·
    refine ⟨12580304662973099156812325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8386869775315399437874883 12580304662973099156812325)
    ·
      refine ⟨2358807124307456091902311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12580304662973099156812325 2358807124307456091902311)
      ·
        refine ⟨3538210686461184137853467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358807124307456091902311 3538210686461184137853467)
        ·
          refine ⟨5307316029691776206780201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3538210686461184137853467 5307316029691776206780201)
          ·
            refine ⟨3980487022268832155085151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5307316029691776206780201 3980487022268832155085151)
            ·
              refine ⟨5970730533403248232627727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3980487022268832155085151 5970730533403248232627727)
              ·
                refine ⟨8956095800104872348941591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5970730533403248232627727 8956095800104872348941591)
                ·
                  refine ⟨13434143700157308523412387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8956095800104872348941591 13434143700157308523412387)
                  ·
                    refine ⟨20151215550235962785118581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13434143700157308523412387 20151215550235962785118581)
                    ·
                      refine ⟨1889176457834621511104867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20151215550235962785118581 1889176457834621511104867)
                      ·
                        rfl

theorem cell23_3679158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3679158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679158 prefixEnd_3679158 := by exact prefixLift 3679158
  have htrace : WordTrace (prefixWord ++ tailWord_3679158) baseStart_3679158 baseEnd_3679158 := by
    simpa [prefixWord, tailWord_3679158, baseEnd_3679158] using wordTrace_append hprefix tailTrace_3679158
  have hstable : (prefixWord ++ tailWord_3679158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679158).length < 2 ^ (prefixWord ++ tailWord_3679158).sum := by decide
  have hdescent : baseEnd_3679158 < baseStart_3679158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679163 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 5]
def baseStart_3679163 : Nat := 118140960795 + 3679163 * 2 ^ 59
def prefixEnd_3679163 : Nat := 4983230072969 + 3 ^ 40 * 3679163 * 2
def baseEnd_3679163 : Nat := 1889179025237893991542343

theorem tailTrace_3679163 : CollatzResearch.WordTrace tailWord_3679163 prefixEnd_3679163 1889179025237893991542343 := by
  unfold tailWord_3679163
  simp only [CollatzResearch.WordTrace]
  refine ⟨134190098770028276859930143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89460065846685517906620095 134190098770028276859930143)
  ·
    refine ⟨201285148155042415289895215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134190098770028276859930143 201285148155042415289895215)
    ·
      refine ⟨301927722232563622934842823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201285148155042415289895215 301927722232563622934842823)
      ·
        refine ⟨452891583348845434402264235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301927722232563622934842823 452891583348845434402264235)
        ·
          refine ⟨679337375023268151603396353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452891583348845434402264235 679337375023268151603396353)
          ·
            refine ⟨509503031267451113702547265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 679337375023268151603396353 509503031267451113702547265)
            ·
              refine ⟨382127273450588335276910449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 509503031267451113702547265 382127273450588335276910449)
              ·
                refine ⟨286595455087941251457682837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382127273450588335276910449 286595455087941251457682837)
                ·
                  refine ⟨13434161957247246162078883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 286595455087941251457682837 13434161957247246162078883)
                  ·
                    refine ⟨20151242935870869243118325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13434161957247246162078883 20151242935870869243118325)
                    ·
                      refine ⟨1889179025237893991542343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20151242935870869243118325 1889179025237893991542343)
                      ·
                        rfl

theorem cell23_3679163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 5].length) (baseStart_3679163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679163 prefixEnd_3679163 := by exact prefixLift 3679163
  have htrace : WordTrace (prefixWord ++ tailWord_3679163) baseStart_3679163 baseEnd_3679163 := by
    simpa [prefixWord, tailWord_3679163, baseEnd_3679163] using wordTrace_append hprefix tailTrace_3679163
  have hstable : (prefixWord ++ tailWord_3679163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679163).length < 2 ^ (prefixWord ++ tailWord_3679163).sum := by decide
  have hdescent : baseEnd_3679163 < baseStart_3679163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679172 : List Nat := [2, 3, 3, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_3679172 : Nat := 118140960795 + 3679172 * 2 ^ 59
def prefixEnd_3679172 : Nat := 4983230072969 + 3 ^ 40 * 3679172 * 2
def baseEnd_3679172 : Nat := 1889183646563784456329803

theorem tailTrace_3679172 : CollatzResearch.WordTrace tailWord_3679172 prefixEnd_3679172 1889183646563784456329803 := by
  unfold tailWord_3679172
  simp only [CollatzResearch.WordTrace]
  refine ⟨67095213513497835698503885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89460284684663780931338513 67095213513497835698503885)
  ·
    refine ⟨25160705067561688386938957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67095213513497835698503885 25160705067561688386938957)
    ·
      refine ⟨9435264400335633145102109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25160705067561688386938957 9435264400335633145102109)
      ·
        refine ⟨3538224150125862429413291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9435264400335633145102109 3538224150125862429413291)
        ·
          refine ⟨5307336225188793644119937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3538224150125862429413291 5307336225188793644119937)
          ·
            refine ⟨3980502168891595233089953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5307336225188793644119937 3980502168891595233089953)
            ·
              refine ⟨2985376626668696424817465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3980502168891595233089953 2985376626668696424817465)
              ·
                refine ⟨2239032470001522318613099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2985376626668696424817465 2239032470001522318613099)
                ·
                  refine ⟨3358548705002283477919649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239032470001522318613099 3358548705002283477919649)
                  ·
                    refine ⟨2518911528751712608439737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3358548705002283477919649 2518911528751712608439737)
                    ·
                      refine ⟨1889183646563784456329803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518911528751712608439737 1889183646563784456329803)
                      ·
                        rfl

theorem cell23_3679172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_3679172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679172 prefixEnd_3679172 := by exact prefixLift 3679172
  have htrace : WordTrace (prefixWord ++ tailWord_3679172) baseStart_3679172 baseEnd_3679172 := by
    simpa [prefixWord, tailWord_3679172, baseEnd_3679172] using wordTrace_append hprefix tailTrace_3679172
  have hstable : (prefixWord ++ tailWord_3679172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679172).length < 2 ^ (prefixWord ++ tailWord_3679172).sum := by decide
  have hdescent : baseEnd_3679172 < baseStart_3679172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679180 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 1, 6, 3]
def baseStart_3679180 : Nat := 118140960795 + 3679180 * 2 ^ 59
def prefixEnd_3679180 : Nat := 4983230072969 + 3 ^ 40 * 3679180 * 2
def baseEnd_3679180 : Nat := 1889187754409020425029765

theorem tailTrace_3679180 : CollatzResearch.WordTrace tailWord_3679180 prefixEnd_3679180 1889187754409020425029765 := by
  unfold tailWord_3679180
  simp only [CollatzResearch.WordTrace]
  refine ⟨67095359405483344381649497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89460479207311125842199329 67095359405483344381649497)
  ·
    refine ⟨50321519554112508286237123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67095359405483344381649497 50321519554112508286237123)
    ·
      refine ⟨75482279331168762429355685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50321519554112508286237123 75482279331168762429355685)
      ·
        refine ⟨14152927374594142955504191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75482279331168762429355685 14152927374594142955504191)
        ·
          refine ⟨21229391061891214433256287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14152927374594142955504191 21229391061891214433256287)
          ·
            refine ⟨31844086592836821649884431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21229391061891214433256287 31844086592836821649884431)
            ·
              refine ⟨47766129889255232474826647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31844086592836821649884431 47766129889255232474826647)
              ·
                refine ⟨71649194833882848712239971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47766129889255232474826647 71649194833882848712239971)
                ·
                  refine ⟨107473792250824273068359957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71649194833882848712239971 107473792250824273068359957)
                  ·
                    refine ⟨5037834011757387800079373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107473792250824273068359957 5037834011757387800079373)
                    ·
                      refine ⟨1889187754409020425029765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5037834011757387800079373 1889187754409020425029765)
                      ·
                        rfl

theorem cell23_3679180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_3679180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679180 prefixEnd_3679180 := by exact prefixLift 3679180
  have htrace : WordTrace (prefixWord ++ tailWord_3679180) baseStart_3679180 baseEnd_3679180 := by
    simpa [prefixWord, tailWord_3679180, baseEnd_3679180] using wordTrace_append hprefix tailTrace_3679180
  have hstable : (prefixWord ++ tailWord_3679180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679180).length < 2 ^ (prefixWord ++ tailWord_3679180).sum := by decide
  have hdescent : baseEnd_3679180 < baseStart_3679180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679194 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2]
def baseStart_3679194 : Nat := 118140960795 + 3679194 * 2 ^ 59
def prefixEnd_3679194 : Nat := 4983230072969 + 3 ^ 40 * 3679194 * 2
def baseEnd_3679194 : Nat := 1889194943138183370254701

theorem tailTrace_3679194 : CollatzResearch.WordTrace tailWord_3679194 prefixEnd_3679194 1889194943138183370254701 := by
  unfold tailWord_3679194
  simp only [CollatzResearch.WordTrace]
  refine ⟨33547807358228992288577159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89460819621943979436205757 33547807358228992288577159)
  ·
    refine ⟨50321711037343488432865739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33547807358228992288577159 50321711037343488432865739)
    ·
      refine ⟨75482566556015232649298609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50321711037343488432865739 75482566556015232649298609)
      ·
        refine ⟨56611924917011424486973957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75482566556015232649298609 56611924917011424486973957)
        ·
          refine ⟨10614735921939642091307617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56611924917011424486973957 10614735921939642091307617)
          ·
            refine ⟨7961051941454731568480713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10614735921939642091307617 7961051941454731568480713)
            ·
              refine ⟨5970788956091048676360535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7961051941454731568480713 5970788956091048676360535)
              ·
                refine ⟨8956183434136573014540803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5970788956091048676360535 8956183434136573014540803)
                ·
                  refine ⟨13434275151204859521811205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8956183434136573014540803 13434275151204859521811205)
                  ·
                    refine ⟨2518926590850911160339601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13434275151204859521811205 2518926590850911160339601)
                    ·
                      refine ⟨1889194943138183370254701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2518926590850911160339601 1889194943138183370254701)
                      ·
                        rfl

theorem cell23_3679194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_3679194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679194 prefixEnd_3679194 := by exact prefixLift 3679194
  have htrace : WordTrace (prefixWord ++ tailWord_3679194) baseStart_3679194 baseEnd_3679194 := by
    simpa [prefixWord, tailWord_3679194, baseEnd_3679194] using wordTrace_append hprefix tailTrace_3679194
  have hstable : (prefixWord ++ tailWord_3679194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679194).length < 2 ^ (prefixWord ++ tailWord_3679194).sum := by decide
  have hdescent : baseEnd_3679194 < baseStart_3679194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679217 : List Nat := [1, 2, 2, 2, 4, 1, 1, 5, 5]
def baseStart_3679217 : Nat := 118140960795 + 3679217 * 2 ^ 59
def prefixEnd_3679217 : Nat := 4983230072969 + 3 ^ 40 * 3679217 * 2
def baseEnd_3679217 : Nat := 209911861465915197807455

theorem tailTrace_3679217 : CollatzResearch.WordTrace tailWord_3679217 prefixEnd_3679217 209911861465915197807455 := by
  unfold tailWord_3679217
  simp only [CollatzResearch.WordTrace]
  refine ⟨134192068311832644082395905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89461378874555096054930603 134192068311832644082395905)
  ·
    refine ⟨100644051233874483061796929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134192068311832644082395905 100644051233874483061796929)
    ·
      refine ⟨75483038425405862296347697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100644051233874483061796929 75483038425405862296347697)
      ·
        refine ⟨56612278819054396722260773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75483038425405862296347697 56612278819054396722260773)
        ·
          refine ⟨10614802278572699385423895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56612278819054396722260773 10614802278572699385423895)
          ·
            refine ⟨15922203417859049078135843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10614802278572699385423895 15922203417859049078135843)
            ·
              refine ⟨23883305126788573617203765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15922203417859049078135843 23883305126788573617203765)
              ·
                refine ⟨2239059855636428776612853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23883305126788573617203765 2239059855636428776612853)
                ·
                  refine ⟨209911861465915197807455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2239059855636428776612853 209911861465915197807455)
                  ·
                    rfl

theorem cell23_3679217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 5, 5].length) (baseStart_3679217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679217 prefixEnd_3679217 := by exact prefixLift 3679217
  have htrace : WordTrace (prefixWord ++ tailWord_3679217) baseStart_3679217 baseEnd_3679217 := by
    simpa [prefixWord, tailWord_3679217, baseEnd_3679217] using wordTrace_append hprefix tailTrace_3679217
  have hstable : (prefixWord ++ tailWord_3679217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679217).length < 2 ^ (prefixWord ++ tailWord_3679217).sum := by decide
  have hdescent : baseEnd_3679217 < baseStart_3679217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679284 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3679284 : Nat := 118140960795 + 3679284 * 2 ^ 59
def prefixEnd_3679284 : Nat := 4983230072969 + 3 ^ 40 * 3679284 * 2
def baseEnd_3679284 : Nat := 1889241156397088018129287

theorem tailTrace_3679284 : CollatzResearch.WordTrace tailWord_3679284 prefixEnd_3679284 1889241156397088018129287 := by
  unfold tailWord_3679284
  simp only [CollatzResearch.WordTrace]
  refine ⟨67097256001294957262542453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89463008001726609683389937 67097256001294957262542453)
  ·
    refine ⟨6290367750121402243363355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67097256001294957262542453 6290367750121402243363355)
    ·
      refine ⟨9435551625182103365045033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6290367750121402243363355 9435551625182103365045033)
      ·
        refine ⟨7076663718886577523783775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9435551625182103365045033 7076663718886577523783775)
        ·
          refine ⟨10614995578329866285675663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7076663718886577523783775 10614995578329866285675663)
          ·
            refine ⟨15922493367494799428513495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10614995578329866285675663 15922493367494799428513495)
            ·
              refine ⟨23883740051242199142770243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15922493367494799428513495 23883740051242199142770243)
              ·
                refine ⟨35825610076863298714155365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23883740051242199142770243 35825610076863298714155365)
                ·
                  refine ⟨6717301889411868508904131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35825610076863298714155365 6717301889411868508904131)
                  ·
                    refine ⟨10075952834117802763356197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6717301889411868508904131 10075952834117802763356197)
                    ·
                      refine ⟨1889241156397088018129287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10075952834117802763356197 1889241156397088018129287)
                      ·
                        rfl

theorem cell23_3679284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3679284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679284 prefixEnd_3679284 := by exact prefixLift 3679284
  have htrace : WordTrace (prefixWord ++ tailWord_3679284) baseStart_3679284 baseEnd_3679284 := by
    simpa [prefixWord, tailWord_3679284, baseEnd_3679284] using wordTrace_append hprefix tailTrace_3679284
  have hstable : (prefixWord ++ tailWord_3679284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679284).length < 2 ^ (prefixWord ++ tailWord_3679284).sum := by decide
  have hdescent : baseEnd_3679284 < baseStart_3679284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679290 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 8]
def baseStart_3679290 : Nat := 118140960795 + 3679290 * 2 ^ 59
def prefixEnd_3679290 : Nat := 4983230072969 + 3 ^ 40 * 3679290 * 2
def baseEnd_3679290 : Nat := 209916026364557221628251

theorem tailTrace_3679290 : CollatzResearch.WordTrace tailWord_3679290 prefixEnd_3679290 209916026364557221628251 := by
  unfold tailWord_3679290
  simp only [CollatzResearch.WordTrace]
  refine ⟨33548682710142044387450831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89463153893712118366535549 33548682710142044387450831)
  ·
    refine ⟨50323024065213066581176247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33548682710142044387450831 50323024065213066581176247)
    ·
      refine ⟨75484536097819599871764371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50323024065213066581176247 75484536097819599871764371)
      ·
        refine ⟨113226804146729399807646557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75484536097819599871764371 113226804146729399807646557)
        ·
          refine ⟨42460051555023524927867459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113226804146729399807646557 42460051555023524927867459)
          ·
            refine ⟨63690077332535287391801189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42460051555023524927867459 63690077332535287391801189)
            ·
              refine ⟨11941889499850366385962723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63690077332535287391801189 11941889499850366385962723)
              ·
                refine ⟨17912834249775549578944085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11941889499850366385962723 17912834249775549578944085)
                ·
                  refine ⟨209916026364557221628251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17912834249775549578944085 209916026364557221628251)
                  ·
                    rfl

theorem cell23_3679290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 8].length) (baseStart_3679290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679290 prefixEnd_3679290 := by exact prefixLift 3679290
  have htrace : WordTrace (prefixWord ++ tailWord_3679290) baseStart_3679290 baseEnd_3679290 := by
    simpa [prefixWord, tailWord_3679290, baseEnd_3679290] using wordTrace_append hprefix tailTrace_3679290
  have hstable : (prefixWord ++ tailWord_3679290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679290).length < 2 ^ (prefixWord ++ tailWord_3679290).sum := by decide
  have hdescent : baseEnd_3679290 < baseStart_3679290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679318 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_3679318 : Nat := 118140960795 + 3679318 * 2 ^ 59
def prefixEnd_3679318 : Nat := 4983230072969 + 3 ^ 40 * 3679318 * 2
def baseEnd_3679318 : Nat := 1889258614739340885104131

theorem tailTrace_3679318 : CollatzResearch.WordTrace tailWord_3679318 prefixEnd_3679318 1889258614739340885104131 := by
  unfold tailWord_3679318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8387234505279171145738913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89463834722977825554548405 8387234505279171145738913)
  ·
    refine ⟨6290425878959378359304185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8387234505279171145738913 6290425878959378359304185)
    ·
      refine ⟨4717819409219533769478139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6290425878959378359304185 4717819409219533769478139)
      ·
        refine ⟨7076729113829300654217209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4717819409219533769478139 7076729113829300654217209)
        ·
          refine ⟨5307546835371975490662907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7076729113829300654217209 5307546835371975490662907)
          ·
            refine ⟨7961320253057963235994361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307546835371975490662907 7961320253057963235994361)
            ·
              refine ⟨5970990189793472426995771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7961320253057963235994361 5970990189793472426995771)
              ·
                refine ⟨8956485284690208640493657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5970990189793472426995771 8956485284690208640493657)
                ·
                  refine ⟨6717363963517656480370243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8956485284690208640493657 6717363963517656480370243)
                  ·
                    refine ⟨10076045945276484720555365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6717363963517656480370243 10076045945276484720555365)
                    ·
                      refine ⟨1889258614739340885104131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10076045945276484720555365 1889258614739340885104131)
                      ·
                        rfl

theorem cell23_3679318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_3679318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679318 prefixEnd_3679318 := by exact prefixLift 3679318
  have htrace : WordTrace (prefixWord ++ tailWord_3679318) baseStart_3679318 baseEnd_3679318 := by
    simpa [prefixWord, tailWord_3679318, baseEnd_3679318] using wordTrace_append hprefix tailTrace_3679318
  have hstable : (prefixWord ++ tailWord_3679318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679318).length < 2 ^ (prefixWord ++ tailWord_3679318).sum := by decide
  have hdescent : baseEnd_3679318 < baseStart_3679318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679344 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 2, 3, 2]
def baseStart_3679344 : Nat := 118140960795 + 3679344 * 2 ^ 59
def prefixEnd_3679344 : Nat := 4983230072969 + 3 ^ 40 * 3679344 * 2
def baseEnd_3679344 : Nat := 1889271965236357783379011

theorem tailTrace_3679344 : CollatzResearch.WordTrace tailWord_3679344 prefixEnd_3679344 1889271965236357783379011 := by
  unfold tailWord_3679344
  simp only [CollatzResearch.WordTrace]
  refine ⟨67098350191186272386134543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89464466921581696514846057 67098350191186272386134543)
  ·
    refine ⟨100647525286779408579201815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67098350191186272386134543 100647525286779408579201815)
    ·
      refine ⟨150971287930169112868802723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100647525286779408579201815 150971287930169112868802723)
      ·
        refine ⟨226456931895253669303204085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150971287930169112868802723 226456931895253669303204085)
        ·
          refine ⟨21230337365180031497175383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226456931895253669303204085 21230337365180031497175383)
          ·
            refine ⟨31845506047770047245763075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21230337365180031497175383 31845506047770047245763075)
            ·
              refine ⟨47768259071655070868644613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31845506047770047245763075 47768259071655070868644613)
              ·
                refine ⟨8956548575935325787870865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47768259071655070868644613 8956548575935325787870865)
                ·
                  refine ⟨6717411431951494340903149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8956548575935325787870865 6717411431951494340903149)
                  ·
                    refine ⟨2519029286981810377838681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6717411431951494340903149 2519029286981810377838681)
                    ·
                      refine ⟨1889271965236357783379011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2519029286981810377838681 1889271965236357783379011)
                      ·
                        rfl

theorem cell23_3679344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 2, 3, 2].length) (baseStart_3679344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679344 prefixEnd_3679344 := by exact prefixLift 3679344
  have htrace : WordTrace (prefixWord ++ tailWord_3679344) baseStart_3679344 baseEnd_3679344 := by
    simpa [prefixWord, tailWord_3679344, baseEnd_3679344] using wordTrace_append hprefix tailTrace_3679344
  have hstable : (prefixWord ++ tailWord_3679344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679344).length < 2 ^ (prefixWord ++ tailWord_3679344).sum := by decide
  have hdescent : baseEnd_3679344 < baseStart_3679344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679351 : List Nat := [1, 1, 3, 1, 1, 4, 3, 4, 1, 1, 3]
def baseStart_3679351 : Nat := 118140960795 + 3679351 * 2 ^ 59
def prefixEnd_3679351 : Nat := 4983230072969 + 3 ^ 40 * 3679351 * 2
def baseEnd_3679351 : Nat := 1889275559600939255991479

theorem tailTrace_3679351 : CollatzResearch.WordTrace tailWord_3679351 prefixEnd_3679351 1889275559600939255991479 := by
  unfold tailWord_3679351
  simp only [CollatzResearch.WordTrace]
  refine ⟨134196955693347184967773907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89464637128898123311849271 134196955693347184967773907)
  ·
    refine ⟨201295433540020777451660861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134196955693347184967773907 201295433540020777451660861)
    ·
      refine ⟨75485787577507791544372823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201295433540020777451660861 75485787577507791544372823)
      ·
        refine ⟨113228681366261687316559235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75485787577507791544372823 113228681366261687316559235)
        ·
          refine ⟨169843022049392530974838853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113228681366261687316559235 169843022049392530974838853)
          ·
            refine ⟨31845566634261099557782285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169843022049392530974838853 31845566634261099557782285)
            ·
              refine ⟨11942087487847912334168357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31845566634261099557782285 11942087487847912334168357)
              ·
                refine ⟨2239141403971483562656567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11942087487847912334168357 2239141403971483562656567)
                ·
                  refine ⟨3358712105957225343984851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239141403971483562656567 3358712105957225343984851)
                  ·
                    refine ⟨5038068158935838015977277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3358712105957225343984851 5038068158935838015977277)
                    ·
                      refine ⟨1889275559600939255991479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5038068158935838015977277 1889275559600939255991479)
                      ·
                        rfl

theorem cell23_3679351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 1, 1, 3].length) (baseStart_3679351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679351 prefixEnd_3679351 := by exact prefixLift 3679351
  have htrace : WordTrace (prefixWord ++ tailWord_3679351) baseStart_3679351 baseEnd_3679351 := by
    simpa [prefixWord, tailWord_3679351, baseEnd_3679351] using wordTrace_append hprefix tailTrace_3679351
  have hstable : (prefixWord ++ tailWord_3679351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679351).length < 2 ^ (prefixWord ++ tailWord_3679351).sum := by decide
  have hdescent : baseEnd_3679351 < baseStart_3679351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679357 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_3679357 : Nat := 118140960795 + 3679357 * 2 ^ 59
def prefixEnd_3679357 : Nat := 4983230072969 + 3 ^ 40 * 3679357 * 2
def baseEnd_3679357 : Nat := 1889278640484866232516451

theorem tailTrace_3679357 : CollatzResearch.WordTrace tailWord_3679357 prefixEnd_3679357 1889278640484866232516451 := by
  unfold tailWord_3679357
  simp only [CollatzResearch.WordTrace]
  refine ⟨134197174531325447992492325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89464783020883631994994883 134197174531325447992492325)
  ·
    refine ⟨25161970224623521498592311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134197174531325447992492325 25161970224623521498592311)
    ·
      refine ⟨37742955336935282247888467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25161970224623521498592311 37742955336935282247888467)
      ·
        refine ⟨56614433005402923371832701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37742955336935282247888467 56614433005402923371832701)
        ·
          refine ⟨21230412377026096264437263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56614433005402923371832701 21230412377026096264437263)
          ·
            refine ⟨31845618565539144396655895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21230412377026096264437263 31845618565539144396655895)
            ·
              refine ⟨47768427848308716594983843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31845618565539144396655895 47768427848308716594983843)
              ·
                refine ⟨71652641772463074892475765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47768427848308716594983843 71652641772463074892475765)
                ·
                  refine ⟨6717435166168413271169603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71652641772463074892475765 6717435166168413271169603)
                  ·
                    refine ⟨10076152749252619906754405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6717435166168413271169603 10076152749252619906754405)
                    ·
                      refine ⟨1889278640484866232516451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10076152749252619906754405 1889278640484866232516451)
                      ·
                        rfl

theorem cell23_3679357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_3679357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679357 prefixEnd_3679357 := by exact prefixLift 3679357
  have htrace : WordTrace (prefixWord ++ tailWord_3679357) baseStart_3679357 baseEnd_3679357 := by
    simpa [prefixWord, tailWord_3679357, baseEnd_3679357] using wordTrace_append hprefix tailTrace_3679357
  have hstable : (prefixWord ++ tailWord_3679357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679357).length < 2 ^ (prefixWord ++ tailWord_3679357).sum := by decide
  have hdescent : baseEnd_3679357 < baseStart_3679357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679367 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 6, 4]
def baseStart_3679367 : Nat := 118140960795 + 3679367 * 2 ^ 59
def prefixEnd_3679367 : Nat := 4983230072969 + 3 ^ 40 * 3679367 * 2
def baseEnd_3679367 : Nat := 629761258430470397797135

theorem tailTrace_3679367 : CollatzResearch.WordTrace tailWord_3679367 prefixEnd_3679367 629761258430470397797135 := by
  unfold tailWord_3679367
  simp only [CollatzResearch.WordTrace]
  refine ⟨134197539261289219700356355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89465026174192813133570903 134197539261289219700356355)
  ·
    refine ⟨201296308891933829550534533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134197539261289219700356355 201296308891933829550534533)
    ·
      refine ⟨37743057917237593040725225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201296308891933829550534533 37743057917237593040725225)
      ·
        refine ⟨28307293437928194780543919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37743057917237593040725225 28307293437928194780543919)
        ·
          refine ⟨42460940156892292170815879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28307293437928194780543919 42460940156892292170815879)
          ·
            refine ⟨63691410235338438256223819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42460940156892292170815879 63691410235338438256223819)
            ·
              refine ⟨95537115353007657384335729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63691410235338438256223819 95537115353007657384335729)
              ·
                refine ⟨71652836514755743038251797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95537115353007657384335729 71652836514755743038251797)
                ·
                  refine ⟨3358726711629175454918053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71652836514755743038251797 3358726711629175454918053)
                  ·
                    refine ⟨629761258430470397797135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3358726711629175454918053 629761258430470397797135)
                    ·
                      rfl

theorem cell23_3679367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_3679367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679367 prefixEnd_3679367 := by exact prefixLift 3679367
  have htrace : WordTrace (prefixWord ++ tailWord_3679367) baseStart_3679367 baseEnd_3679367 := by
    simpa [prefixWord, tailWord_3679367, baseEnd_3679367] using wordTrace_append hprefix tailTrace_3679367
  have hstable : (prefixWord ++ tailWord_3679367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679367).length < 2 ^ (prefixWord ++ tailWord_3679367).sum := by decide
  have hdescent : baseEnd_3679367 < baseStart_3679367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679374 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3679374 : Nat := 118140960795 + 3679374 * 2 ^ 59
def prefixEnd_3679374 : Nat := 4983230072969 + 3 ^ 40 * 3679374 * 2
def baseEnd_3679374 : Nat := 1889287369655992666003873

theorem tailTrace_3679374 : CollatzResearch.WordTrace tailWord_3679374 prefixEnd_3679374 1889287369655992666003873 := by
  unfold tailWord_3679374
  simp only [CollatzResearch.WordTrace]
  refine ⟨16774724321532982486982647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89465196381509239930574117 16774724321532982486982647)
  ·
    refine ⟨25162086482299473730473971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16774724321532982486982647 25162086482299473730473971)
    ·
      refine ⟨37743129723449210595710957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25162086482299473730473971 37743129723449210595710957)
      ·
        refine ⟨14153673646293453973391609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37743129723449210595710957 14153673646293453973391609)
        ·
          refine ⟨10615255234720090480043707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14153673646293453973391609 10615255234720090480043707)
          ·
            refine ⟨15922882852080135720065561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10615255234720090480043707 15922882852080135720065561)
            ·
              refine ⟨11942162139060101790049171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15922882852080135720065561 11942162139060101790049171)
              ·
                refine ⟨17913243208590152685073757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11942162139060101790049171 17913243208590152685073757)
                ·
                  refine ⟨6717466203221307256902659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17913243208590152685073757 6717466203221307256902659)
                  ·
                    refine ⟨10076199304831960885353989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6717466203221307256902659 10076199304831960885353989)
                    ·
                      refine ⟨1889287369655992666003873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10076199304831960885353989 1889287369655992666003873)
                      ·
                        rfl

theorem cell23_3679374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3679374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679374 prefixEnd_3679374 := by exact prefixLift 3679374
  have htrace : WordTrace (prefixWord ++ tailWord_3679374) baseStart_3679374 baseEnd_3679374 := by
    simpa [prefixWord, tailWord_3679374, baseEnd_3679374] using wordTrace_append hprefix tailTrace_3679374
  have hstable : (prefixWord ++ tailWord_3679374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679374).length < 2 ^ (prefixWord ++ tailWord_3679374).sum := by decide
  have hdescent : baseEnd_3679374 < baseStart_3679374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679378 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_3679378 : Nat := 118140960795 + 3679378 * 2 ^ 59
def prefixEnd_3679378 : Nat := 4983230072969 + 3 ^ 40 * 3679378 * 2
def baseEnd_3679378 : Nat := 1889289423578610650353855

theorem tailTrace_3679378 : CollatzResearch.WordTrace tailWord_3679378 prefixEnd_3679378 1889289423578610650353855 := by
  unfold tailWord_3679378
  simp only [CollatzResearch.WordTrace]
  refine ⟨33549485116062342144751697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89465293642832912386004525 33549485116062342144751697)
  ·
    refine ⟨25162113837046756608563773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33549485116062342144751697 25162113837046756608563773)
    ·
      refine ⟨9435792688892533728211415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25162113837046756608563773 9435792688892533728211415)
      ·
        refine ⟨14153689033338800592317123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9435792688892533728211415 14153689033338800592317123)
        ·
          refine ⟨21230533550008200888475685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14153689033338800592317123 21230533550008200888475685)
          ·
            refine ⟨3980725040626537666589191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21230533550008200888475685 3980725040626537666589191)
            ·
              refine ⟨5971087560939806499883787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3980725040626537666589191 5971087560939806499883787)
              ·
                refine ⟨8956631341409709749825681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5971087560939806499883787 8956631341409709749825681)
                ·
                  refine ⟨6717473506057282312369261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8956631341409709749825681 6717473506057282312369261)
                  ·
                    refine ⟨2519052564771480867138473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6717473506057282312369261 2519052564771480867138473)
                    ·
                      refine ⟨1889289423578610650353855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2519052564771480867138473 1889289423578610650353855)
                      ·
                        rfl

theorem cell23_3679378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_3679378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679378 prefixEnd_3679378 := by exact prefixLift 3679378
  have htrace : WordTrace (prefixWord ++ tailWord_3679378) baseStart_3679378 baseEnd_3679378 := by
    simpa [prefixWord, tailWord_3679378, baseEnd_3679378] using wordTrace_append hprefix tailTrace_3679378
  have hstable : (prefixWord ++ tailWord_3679378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679378).length < 2 ^ (prefixWord ++ tailWord_3679378).sum := by decide
  have hdescent : baseEnd_3679378 < baseStart_3679378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679391 : List Nat := [1, 1, 2, 6, 2, 1, 1, 3, 1, 1, 4]
def baseStart_3679391 : Nat := 118140960795 + 3679391 * 2 ^ 59
def prefixEnd_3679391 : Nat := 4983230072969 + 3 ^ 40 * 3679391 * 2
def baseEnd_3679391 : Nat := 1889296098827119099491295

theorem tailTrace_3679391 : CollatzResearch.WordTrace tailWord_3679391 prefixEnd_3679391 1889296098827119099491295 := by
  unfold tailWord_3679391
  simp only [CollatzResearch.WordTrace]
  refine ⟨134198414613202271799230027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89465609742134847866153351 134198414613202271799230027)
  ·
    refine ⟨201297621919803407698845041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134198414613202271799230027 201297621919803407698845041)
    ·
      refine ⟨150973216439852555774133781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201297621919803407698845041 150973216439852555774133781)
      ·
        refine ⟨7076869520618088551912521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150973216439852555774133781 7076869520618088551912521)
        ·
          refine ⟨5307652140463566413934391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7076869520618088551912521 5307652140463566413934391)
          ·
            refine ⟨7961478210695349620901587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307652140463566413934391 7961478210695349620901587)
            ·
              refine ⟨11942217316043024431352381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7961478210695349620901587 11942217316043024431352381)
              ·
                refine ⟨4478331493516134161757143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11942217316043024431352381 4478331493516134161757143)
                ·
                  refine ⟨6717497240274201242635715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4478331493516134161757143 6717497240274201242635715)
                  ·
                    refine ⟨10076245860411301863953573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6717497240274201242635715 10076245860411301863953573)
                    ·
                      refine ⟨1889296098827119099491295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10076245860411301863953573 1889296098827119099491295)
                      ·
                        rfl

theorem cell23_3679391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_3679391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679391 prefixEnd_3679391 := by exact prefixLift 3679391
  have htrace : WordTrace (prefixWord ++ tailWord_3679391) baseStart_3679391 baseEnd_3679391 := by
    simpa [prefixWord, tailWord_3679391, baseEnd_3679391] using wordTrace_append hprefix tailTrace_3679391
  have hstable : (prefixWord ++ tailWord_3679391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679391).length < 2 ^ (prefixWord ++ tailWord_3679391).sum := by decide
  have hdescent : baseEnd_3679391 < baseStart_3679391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679407 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 3]
def baseStart_3679407 : Nat := 118140960795 + 3679407 * 2 ^ 59
def prefixEnd_3679407 : Nat := 4983230072969 + 3 ^ 40 * 3679407 * 2
def baseEnd_3679407 : Nat := 1889304314517591036891221

theorem tailTrace_3679407 : CollatzResearch.WordTrace tailWord_3679407 prefixEnd_3679407 1889304314517591036891221 := by
  unfold tailWord_3679407
  simp only [CollatzResearch.WordTrace]
  refine ⟨134198998181144306531812475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89465998787429537687874983 134198998181144306531812475)
  ·
    refine ⟨201298497271716459797718713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134198998181144306531812475 201298497271716459797718713)
    ·
      refine ⟨150973872953787344848289035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201298497271716459797718713 150973872953787344848289035)
      ·
        refine ⟨226460809430681017272433553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150973872953787344848289035 226460809430681017272433553)
        ·
          refine ⟨169845607073010762954325165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226460809430681017272433553 169845607073010762954325165)
          ·
            refine ⟨63692102652379036107871937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169845607073010762954325165 63692102652379036107871937)
            ·
              refine ⟨47769076989284277080903953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63692102652379036107871937 47769076989284277080903953)
              ·
                refine ⟨35826807741963207810677965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47769076989284277080903953 35826807741963207810677965)
                ·
                  refine ⟨13435052903236202929004237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35826807741963207810677965 13435052903236202929004237)
                  ·
                    refine ⟨5038144838713576098376589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13435052903236202929004237 5038144838713576098376589)
                    ·
                      refine ⟨1889304314517591036891221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5038144838713576098376589 1889304314517591036891221)
                      ·
                        rfl

theorem cell23_3679407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 3].length) (baseStart_3679407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679407 prefixEnd_3679407 := by exact prefixLift 3679407
  have htrace : WordTrace (prefixWord ++ tailWord_3679407) baseStart_3679407 baseEnd_3679407 := by
    simpa [prefixWord, tailWord_3679407, baseEnd_3679407] using wordTrace_append hprefix tailTrace_3679407
  have hstable : (prefixWord ++ tailWord_3679407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679407).length < 2 ^ (prefixWord ++ tailWord_3679407).sum := by decide
  have hdescent : baseEnd_3679407 < baseStart_3679407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679428 : List Nat := [2, 3, 3, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_3679428 : Nat := 118140960795 + 3679428 * 2 ^ 59
def prefixEnd_3679428 : Nat := 4983230072969 + 3 ^ 40 * 3679428 * 2
def baseEnd_3679428 : Nat := 1889315097611335454728625

theorem tailTrace_3679428 : CollatzResearch.WordTrace tailWord_3679428 prefixEnd_3679428 1889315097611335454728625 := by
  unfold tailWord_3679428
  simp only [CollatzResearch.WordTrace]
  refine ⟨67099882057034113559163469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89466509409378818078884625 67099882057034113559163469)
  ·
    refine ⟨25162455771387792584686301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67099882057034113559163469 25162455771387792584686301)
    ·
      refine ⟨9435920914270422219257363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25162455771387792584686301 9435920914270422219257363)
      ·
        refine ⟨14153881371405633328886045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9435920914270422219257363 14153881371405633328886045)
        ·
          refine ⟨5307705514277112498332267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14153881371405633328886045 5307705514277112498332267)
          ·
            refine ⟨7961558271415668747498401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307705514277112498332267 7961558271415668747498401)
            ·
              refine ⟨5971168703561751560623801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7961558271415668747498401 5971168703561751560623801)
              ·
                refine ⟨4478376527671313670467851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5971168703561751560623801 4478376527671313670467851)
                ·
                  refine ⟨6717564791506970505701777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4478376527671313670467851 6717564791506970505701777)
                  ·
                    refine ⟨5038173593630227879276333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6717564791506970505701777 5038173593630227879276333)
                    ·
                      refine ⟨1889315097611335454728625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5038173593630227879276333 1889315097611335454728625)
                      ·
                        rfl

theorem cell23_3679428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_3679428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679428 prefixEnd_3679428 := by exact prefixLift 3679428
  have htrace : WordTrace (prefixWord ++ tailWord_3679428) baseStart_3679428 baseEnd_3679428 := by
    simpa [prefixWord, tailWord_3679428, baseEnd_3679428] using wordTrace_append hprefix tailTrace_3679428
  have hstable : (prefixWord ++ tailWord_3679428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679428).length < 2 ^ (prefixWord ++ tailWord_3679428).sum := by decide
  have hdescent : baseEnd_3679428 < baseStart_3679428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679551 : List Nat := [1, 1, 2, 2, 4, 4, 1, 1, 2, 5]
def baseStart_3679551 : Nat := 118140960795 + 3679551 * 2 ^ 59
def prefixEnd_3679551 : Nat := 4983230072969 + 3 ^ 40 * 3679551 * 2
def baseEnd_3679551 : Nat := 629792751910612824496853

theorem tailTrace_3679551 : CollatzResearch.WordTrace tailWord_3679551 prefixEnd_3679551 629792751910612824496853 := by
  unfold tailWord_3679551
  simp only [CollatzResearch.WordTrace]
  refine ⟨134204250292622619125054507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89469500195081746083369671 134204250292622619125054507)
  ·
    refine ⟨201306375438933928687581761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134204250292622619125054507 201306375438933928687581761)
    ·
      refine ⟨150979781579200446515686321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201306375438933928687581761 150979781579200446515686321)
      ·
        refine ⟨113234836184400334886764741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150979781579200446515686321 113234836184400334886764741)
        ·
          refine ⟨21231531784575062791268389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113234836184400334886764741 21231531784575062791268389)
          ·
            refine ⟨3980912209607824273362823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21231531784575062791268389 3980912209607824273362823)
            ·
              refine ⟨5971368314411736410044235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3980912209607824273362823 5971368314411736410044235)
              ·
                refine ⟨8957052471617604615066353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5971368314411736410044235 8957052471617604615066353)
                ·
                  refine ⟨6717789353713203461299765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8957052471617604615066353 6717789353713203461299765)
                  ·
                    refine ⟨629792751910612824496853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6717789353713203461299765 629792751910612824496853)
                    ·
                      rfl

theorem cell23_3679551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 5].length) (baseStart_3679551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679551 prefixEnd_3679551 := by exact prefixLift 3679551
  have htrace : WordTrace (prefixWord ++ tailWord_3679551) baseStart_3679551 baseEnd_3679551 := by
    simpa [prefixWord, tailWord_3679551, baseEnd_3679551] using wordTrace_append hprefix tailTrace_3679551
  have hstable : (prefixWord ++ tailWord_3679551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679551).length < 2 ^ (prefixWord ++ tailWord_3679551).sum := by decide
  have hdescent : baseEnd_3679551 < baseStart_3679551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679621 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 5, 1, 3]
def baseStart_3679621 : Nat := 118140960795 + 3679621 * 2 ^ 59
def prefixEnd_3679621 : Nat := 4983230072969 + 3 ^ 40 * 3679621 * 2
def baseEnd_3679621 : Nat := 1889414199377653199615237

theorem tailTrace_3679621 : CollatzResearch.WordTrace tailWord_3679621 prefixEnd_3679621 1889414199377653199615237 := by
  unfold tailWord_3679621
  simp only [CollatzResearch.WordTrace]
  refine ⟨134206803402369021080102717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89471202268246014053401811 134206803402369021080102717)
  ·
    refine ⟨50327551275888382905038519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134206803402369021080102717 50327551275888382905038519)
    ·
      refine ⟨75491326913832574357557779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50327551275888382905038519 75491326913832574357557779)
      ·
        refine ⟨113236990370748861536336669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75491326913832574357557779 113236990370748861536336669)
        ·
          refine ⟨42463871389030823076126251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113236990370748861536336669 42463871389030823076126251)
          ·
            refine ⟨63695807083546234614189377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42463871389030823076126251 63695807083546234614189377)
            ·
              refine ⟨47771855312659675960642033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63695807083546234614189377 47771855312659675960642033)
              ·
                refine ⟨35828891484494756970481525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47771855312659675960642033 35828891484494756970481525)
                ·
                  refine ⟨3358958576671383465982643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35828891484494756970481525 3358958576671383465982643)
                  ·
                    refine ⟨5038437865007075198973965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3358958576671383465982643 5038437865007075198973965)
                    ·
                      refine ⟨1889414199377653199615237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5038437865007075198973965 1889414199377653199615237)
                      ·
                        rfl

theorem cell23_3679621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_3679621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679621 prefixEnd_3679621 := by exact prefixLift 3679621
  have htrace : WordTrace (prefixWord ++ tailWord_3679621) baseStart_3679621 baseEnd_3679621 := by
    simpa [prefixWord, tailWord_3679621, baseEnd_3679621] using wordTrace_append hprefix tailTrace_3679621
  have hstable : (prefixWord ++ tailWord_3679621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679621).length < 2 ^ (prefixWord ++ tailWord_3679621).sum := by decide
  have hdescent : baseEnd_3679621 < baseStart_3679621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679688 : List Nat := [2, 1, 3, 1, 3, 1, 4, 2, 2, 4]
def baseStart_3679688 : Nat := 118140960795 + 3679688 * 2 ^ 59
def prefixEnd_3679688 : Nat := 4983230072969 + 3 ^ 40 * 3679688 * 2
def baseEnd_3679688 : Nat := 629816200860501479159143

theorem tailTrace_3679688 : CollatzResearch.WordTrace tailWord_3679688 prefixEnd_3679688 629816200860501479159143 := by
  unfold tailWord_3679688
  simp only [CollatzResearch.WordTrace]
  refine ⟨67104623546563145761395859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89472831395417527681861145 67104623546563145761395859)
  ·
    refine ⟨100656935319844718642093789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67104623546563145761395859 100656935319844718642093789)
    ·
      refine ⟨37746350744941769490785171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100656935319844718642093789 37746350744941769490785171)
      ·
        refine ⟨56619526117412654236177757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37746350744941769490785171 56619526117412654236177757)
        ·
          refine ⟨21232322294029745338566659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56619526117412654236177757 21232322294029745338566659)
          ·
            refine ⟨31848483441044618007849989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21232322294029745338566659 31848483441044618007849989)
            ·
              refine ⟨5971590645195865876471873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31848483441044618007849989 5971590645195865876471873)
              ·
                refine ⟨4478692983896899407353905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5971590645195865876471873 4478692983896899407353905)
                ·
                  refine ⟨3359019737922674555515429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4478692983896899407353905 3359019737922674555515429)
                  ·
                    refine ⟨629816200860501479159143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3359019737922674555515429 629816200860501479159143)
                    ·
                      rfl

theorem cell23_3679688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_3679688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679688 prefixEnd_3679688 := by exact prefixLift 3679688
  have htrace : WordTrace (prefixWord ++ tailWord_3679688) baseStart_3679688 baseEnd_3679688 := by
    simpa [prefixWord, tailWord_3679688, baseEnd_3679688] using wordTrace_append hprefix tailTrace_3679688
  have hstable : (prefixWord ++ tailWord_3679688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679688).length < 2 ^ (prefixWord ++ tailWord_3679688).sum := by decide
  have hdescent : baseEnd_3679688 < baseStart_3679688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679704 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_3679704 : Nat := 118140960795 + 3679704 * 2 ^ 59
def prefixEnd_3679704 : Nat := 4983230072969 + 3 ^ 40 * 3679704 * 2
def baseEnd_3679704 : Nat := 1889456818271976374877355

theorem tailTrace_3679704 : CollatzResearch.WordTrace tailWord_3679704 prefixEnd_3679704 1889456818271976374877355 := by
  unfold tailWord_3679704
  simp only [CollatzResearch.WordTrace]
  refine ⟨67104915330534163127687083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89473220440712217503582777 67104915330534163127687083)
  ·
    refine ⟨100657372995801244691530625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67104915330534163127687083 100657372995801244691530625)
    ·
      refine ⟨75493029746850933518647969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100657372995801244691530625 75493029746850933518647969)
      ·
        refine ⟨56619772310138200138985977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75493029746850933518647969 56619772310138200138985977)
        ·
          refine ⟨42464829232603650104239483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56619772310138200138985977 42464829232603650104239483)
          ·
            refine ⟨63697243848905475156359225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42464829232603650104239483 63697243848905475156359225)
            ·
              refine ⟨47772932886679106367269419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63697243848905475156359225 47772932886679106367269419)
              ·
                refine ⟨71659399330018659550904129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47772932886679106367269419 71659399330018659550904129)
                ·
                  refine ⟨53744549497513994663178097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71659399330018659550904129 53744549497513994663178097)
                  ·
                    refine ⟨40308412123135495997383573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53744549497513994663178097 40308412123135495997383573)
                    ·
                      refine ⟨1889456818271976374877355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40308412123135495997383573 1889456818271976374877355)
                      ·
                        rfl

theorem cell23_3679704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_3679704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679704 prefixEnd_3679704 := by exact prefixLift 3679704
  have htrace : WordTrace (prefixWord ++ tailWord_3679704) baseStart_3679704 baseEnd_3679704 := by
    simpa [prefixWord, tailWord_3679704, baseEnd_3679704] using wordTrace_append hprefix tailTrace_3679704
  have hstable : (prefixWord ++ tailWord_3679704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679704).length < 2 ^ (prefixWord ++ tailWord_3679704).sum := by decide
  have hdescent : baseEnd_3679704 < baseStart_3679704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679745 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_3679745 : Nat := 118140960795 + 3679745 * 2 ^ 59
def prefixEnd_3679745 : Nat := 4983230072969 + 3 ^ 40 * 3679745 * 2
def baseEnd_3679745 : Nat := 1889477870978810714464667

theorem tailTrace_3679745 : CollatzResearch.WordTrace tailWord_3679745 prefixEnd_3679745 1889477870978810714464667 := by
  unfold tailWord_3679745
  simp only [CollatzResearch.WordTrace]
  refine ⟨134211326053919790257616689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89474217369279860171744459 134211326053919790257616689)
  ·
    refine ⟨100658494540439842693212517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134211326053919790257616689 100658494540439842693212517)
    ·
      refine ⟨18873467726332470504977347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100658494540439842693212517 18873467726332470504977347)
      ·
        refine ⟨28310201589498705757466021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18873467726332470504977347 28310201589498705757466021)
        ·
          refine ⟨5308162798031007329524879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28310201589498705757466021 5308162798031007329524879)
          ·
            refine ⟨7962244197046510994287319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5308162798031007329524879 7962244197046510994287319)
            ·
              refine ⟨11943366295569766491430979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7962244197046510994287319 11943366295569766491430979)
              ·
                refine ⟨17915049443354649737146469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11943366295569766491430979 17915049443354649737146469)
                ·
                  refine ⟨3359071770628996825714963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17915049443354649737146469 3359071770628996825714963)
                  ·
                    refine ⟨5038607655943495238572445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3359071770628996825714963 5038607655943495238572445)
                    ·
                      refine ⟨1889477870978810714464667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5038607655943495238572445 1889477870978810714464667)
                      ·
                        rfl

theorem cell23_3679745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_3679745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679745 prefixEnd_3679745 := by exact prefixLift 3679745
  have htrace : WordTrace (prefixWord ++ tailWord_3679745) baseStart_3679745 baseEnd_3679745 := by
    simpa [prefixWord, tailWord_3679745, baseEnd_3679745] using wordTrace_append hprefix tailTrace_3679745
  have hstable : (prefixWord ++ tailWord_3679745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679745).length < 2 ^ (prefixWord ++ tailWord_3679745).sum := by decide
  have hdescent : baseEnd_3679745 < baseStart_3679745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679848 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3679848 : Nat := 118140960795 + 3679848 * 2 ^ 59
def prefixEnd_3679848 : Nat := 4983230072969 + 3 ^ 40 * 3679848 * 2
def baseEnd_3679848 : Nat := 1889530759486223811476693

theorem tailTrace_3679848 : CollatzResearch.WordTrace tailWord_3679848 prefixEnd_3679848 1889530759486223811476693 := by
  unfold tailWord_3679848
  simp only [CollatzResearch.WordTrace]
  refine ⟨67107541386273319424308099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89476721848364425899077465 67107541386273319424308099)
  ·
    refine ⟨100661312079409979136462149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67107541386273319424308099 100661312079409979136462149)
    ·
      refine ⟨18873996014889371088086653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100661312079409979136462149 18873996014889371088086653)
      ·
        refine ⟨7077748505583514158032495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18873996014889371088086653 7077748505583514158032495)
        ·
          refine ⟨10616622758375271237048743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7077748505583514158032495 10616622758375271237048743)
          ·
            refine ⟨15924934137562906855573115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10616622758375271237048743 15924934137562906855573115)
            ·
              refine ⟨23887401206344360283359673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15924934137562906855573115 23887401206344360283359673)
              ·
                refine ⟨17915550904758270212519755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23887401206344360283359673 17915550904758270212519755)
                ·
                  refine ⟨26873326357137405318779633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17915550904758270212519755 26873326357137405318779633)
                  ·
                    refine ⟨20154994767853053989084725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26873326357137405318779633 20154994767853053989084725)
                    ·
                      refine ⟨1889530759486223811476693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20154994767853053989084725 1889530759486223811476693)
                      ·
                        rfl

theorem cell23_3679848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3679848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679848 prefixEnd_3679848 := by exact prefixLift 3679848
  have htrace : WordTrace (prefixWord ++ tailWord_3679848) baseStart_3679848 baseEnd_3679848 := by
    simpa [prefixWord, tailWord_3679848, baseEnd_3679848] using wordTrace_append hprefix tailTrace_3679848
  have hstable : (prefixWord ++ tailWord_3679848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679848).length < 2 ^ (prefixWord ++ tailWord_3679848).sum := by decide
  have hdescent : baseEnd_3679848 < baseStart_3679848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679868 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 3, 4]
def baseStart_3679868 : Nat := 118140960795 + 3679868 * 2 ^ 59
def prefixEnd_3679868 : Nat := 4983230072969 + 3 ^ 40 * 3679868 * 2
def baseEnd_3679868 : Nat := 629847009699771244408867

theorem tailTrace_3679868 : CollatzResearch.WordTrace tailWord_3679868 prefixEnd_3679868 629847009699771244408867 := by
  unfold tailWord_3679868
  simp only [CollatzResearch.WordTrace]
  refine ⟨67107906116237091132172129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89477208154982788176229505 67107906116237091132172129)
  ·
    refine ⟨50330929587177818349129097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67107906116237091132172129 50330929587177818349129097)
    ·
      refine ⟨37748197190383363761846823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50330929587177818349129097 37748197190383363761846823)
      ·
        refine ⟨56622295785575045642770235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37748197190383363761846823 56622295785575045642770235)
        ·
          refine ⟨84933443678362568464155353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56622295785575045642770235 84933443678362568464155353)
          ·
            refine ⟨63700082758771926348116515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84933443678362568464155353 63700082758771926348116515)
            ·
              refine ⟨95550124138157889522174773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63700082758771926348116515 95550124138157889522174773)
              ·
                refine ⟨8957824137952302142703885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95550124138157889522174773 8957824137952302142703885)
                ·
                  refine ⟨3359184051732113303513957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8957824137952302142703885 3359184051732113303513957)
                  ·
                    refine ⟨629847009699771244408867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3359184051732113303513957 629847009699771244408867)
                    ·
                      rfl

theorem cell23_3679868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_3679868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679868 prefixEnd_3679868 := by exact prefixLift 3679868
  have htrace : WordTrace (prefixWord ++ tailWord_3679868) baseStart_3679868 baseEnd_3679868 := by
    simpa [prefixWord, tailWord_3679868, baseEnd_3679868] using wordTrace_append hprefix tailTrace_3679868
  have hstable : (prefixWord ++ tailWord_3679868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679868).length < 2 ^ (prefixWord ++ tailWord_3679868).sum := by decide
  have hdescent : baseEnd_3679868 < baseStart_3679868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679895 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 3]
def baseStart_3679895 : Nat := 118140960795 + 3679895 * 2 ^ 59
def prefixEnd_3679895 : Nat := 4983230072969 + 3 ^ 40 * 3679895 * 2
def baseEnd_3679895 : Nat := 1889554893076985127588977

theorem tailTrace_3679895 : CollatzResearch.WordTrace tailWord_3679895 prefixEnd_3679895 1889554893076985127588977 := by
  unfold tailWord_3679895
  simp only [CollatzResearch.WordTrace]
  refine ⟨134216797003376365875577139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89477864668917577250384759 134216797003376365875577139)
  ·
    refine ⟨201325195505064548813365709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134216797003376365875577139 201325195505064548813365709)
    ·
      refine ⟨75496948314399205805012141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201325195505064548813365709 75496948314399205805012141)
      ·
        refine ⟨28311355617899702176879553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75496948314399205805012141 28311355617899702176879553)
        ·
          refine ⟨21233516713424776632659665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28311355617899702176879553 21233516713424776632659665)
          ·
            refine ⟨15925137535068582474494749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21233516713424776632659665 15925137535068582474494749)
            ·
              refine ⟨5971926575650718427935531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15925137535068582474494749 5971926575650718427935531)
              ·
                refine ⟨8957889863476077641903297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5971926575650718427935531 8957889863476077641903297)
                ·
                  refine ⟨6718417397607058231427473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8957889863476077641903297 6718417397607058231427473)
                  ·
                    refine ⟨5038813048205293673570605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6718417397607058231427473 5038813048205293673570605)
                    ·
                      refine ⟨1889554893076985127588977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5038813048205293673570605 1889554893076985127588977)
                      ·
                        rfl

theorem cell23_3679895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_3679895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679895 prefixEnd_3679895 := by exact prefixLift 3679895
  have htrace : WordTrace (prefixWord ++ tailWord_3679895) baseStart_3679895 baseEnd_3679895 := by
    simpa [prefixWord, tailWord_3679895, baseEnd_3679895] using wordTrace_append hprefix tailTrace_3679895
  have hstable : (prefixWord ++ tailWord_3679895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679895).length < 2 ^ (prefixWord ++ tailWord_3679895).sum := by decide
  have hdescent : baseEnd_3679895 < baseStart_3679895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679968 : List Nat := [2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 5]
def baseStart_3679968 : Nat := 118140960795 + 3679968 * 2 ^ 59
def prefixEnd_3679968 : Nat := 4983230072969 + 3 ^ 40 * 3679968 * 2
def baseEnd_3679968 : Nat := 1889592377164763341976141

theorem tailTrace_3679968 : CollatzResearch.WordTrace tailWord_3679968 prefixEnd_3679968 1889592377164763341976141 := by
  unfold tailWord_3679968
  simp only [CollatzResearch.WordTrace]
  refine ⟨67109729766055949671492279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89479639688074599561989705 67109729766055949671492279)
  ·
    refine ⟨100664594649083924507238419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67109729766055949671492279 100664594649083924507238419)
    ·
      refine ⟨150996891973625886760857629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100664594649083924507238419 150996891973625886760857629)
      ·
        refine ⟨56623834490109707535321611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150996891973625886760857629 56623834490109707535321611)
        ·
          refine ⟨84935751735164561302982417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56623834490109707535321611 84935751735164561302982417)
          ·
            refine ⟨63701813801373420977236813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84935751735164561302982417 63701813801373420977236813)
            ·
              refine ⟨23888180175515032866463805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63701813801373420977236813 23888180175515032866463805)
              ·
                refine ⟨8958067565818137324923927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23888180175515032866463805 8958067565818137324923927)
                ·
                  refine ⟨13437101348727205987385891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8958067565818137324923927 13437101348727205987385891)
                  ·
                    refine ⟨20155652023090808981078837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13437101348727205987385891 20155652023090808981078837)
                    ·
                      refine ⟨1889592377164763341976141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20155652023090808981078837 1889592377164763341976141)
                      ·
                        rfl

theorem cell23_3679968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_3679968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679968 prefixEnd_3679968 := by exact prefixLift 3679968
  have htrace : WordTrace (prefixWord ++ tailWord_3679968) baseStart_3679968 baseEnd_3679968 := by
    simpa [prefixWord, tailWord_3679968, baseEnd_3679968] using wordTrace_append hprefix tailTrace_3679968
  have hstable : (prefixWord ++ tailWord_3679968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679968).length < 2 ^ (prefixWord ++ tailWord_3679968).sum := by decide
  have hdescent : baseEnd_3679968 < baseStart_3679968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679976 : List Nat := [2, 1, 4, 1, 3, 2, 3, 2, 1, 1, 3]
def baseStart_3679976 : Nat := 118140960795 + 3679976 * 2 ^ 59
def prefixEnd_3679976 : Nat := 4983230072969 + 3 ^ 40 * 3679976 * 2
def baseEnd_3679976 : Nat := 1889596485009999310676105

theorem tailTrace_3679976 : CollatzResearch.WordTrace tailWord_3679976 prefixEnd_3679976 1889596485009999310676105 := by
  unfold tailWord_3679976
  simp only [CollatzResearch.WordTrace]
  refine ⟨67109875658041458354637891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89479834210721944472850521 67109875658041458354637891)
  ·
    refine ⟨100664813487062187531956837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67109875658041458354637891 100664813487062187531956837)
    ·
      refine ⟨18874652528824160162241907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100664813487062187531956837 18874652528824160162241907)
      ·
        refine ⟨28311978793236240243362861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18874652528824160162241907 28311978793236240243362861)
        ·
          refine ⟨10616992047463590091261073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28311978793236240243362861 10616992047463590091261073)
          ·
            refine ⟨7962744035597692568445805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10616992047463590091261073 7962744035597692568445805)
            ·
              refine ⟨2986029013349134713167177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7962744035597692568445805 2986029013349134713167177)
              ·
                refine ⟨2239521760011851034875383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2986029013349134713167177 2239521760011851034875383)
                ·
                  refine ⟨3359282640017776552313075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239521760011851034875383 3359282640017776552313075)
                  ·
                    refine ⟨5038923960026664828469613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3359282640017776552313075 5038923960026664828469613)
                    ·
                      refine ⟨1889596485009999310676105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5038923960026664828469613 1889596485009999310676105)
                      ·
                        rfl

theorem cell23_3679976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_3679976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679976 prefixEnd_3679976 := by exact prefixLift 3679976
  have htrace : WordTrace (prefixWord ++ tailWord_3679976) baseStart_3679976 baseEnd_3679976 := by
    simpa [prefixWord, tailWord_3679976, baseEnd_3679976] using wordTrace_append hprefix tailTrace_3679976
  have hstable : (prefixWord ++ tailWord_3679976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679976).length < 2 ^ (prefixWord ++ tailWord_3679976).sum := by decide
  have hdescent : baseEnd_3679976 < baseStart_3679976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3679978 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_3679978 : Nat := 118140960795 + 3679978 * 2 ^ 59
def prefixEnd_3679978 : Nat := 4983230072969 + 3 ^ 40 * 3679978 * 2
def baseEnd_3679978 : Nat := 1889597511971308302851095

theorem tailTrace_3679978 : CollatzResearch.WordTrace tailWord_3679978 prefixEnd_3679978 1889597511971308302851095 := by
  unfold tailWord_3679978
  simp only [CollatzResearch.WordTrace]
  refine ⟨33554956065518917762712147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89479882841383780700565725 33554956065518917762712147)
  ·
    refine ⟨50332434098278376644068221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33554956065518917762712147 50332434098278376644068221)
    ·
      refine ⟨18874662786854391241525583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50332434098278376644068221 18874662786854391241525583)
      ·
        refine ⟨28311994180281586862288375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18874662786854391241525583 28311994180281586862288375)
        ·
          refine ⟨42467991270422380293432563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28311994180281586862288375 42467991270422380293432563)
          ·
            refine ⟨63701986905633570440148845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42467991270422380293432563 63701986905633570440148845)
            ·
              refine ⟨23888245089612588915055817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63701986905633570440148845 23888245089612588915055817)
              ·
                refine ⟨17916183817209441686291863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23888245089612588915055817 17916183817209441686291863)
                ·
                  refine ⟨26874275725814162529437795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17916183817209441686291863 26874275725814162529437795)
                  ·
                    refine ⟨40311413588721243794156693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26874275725814162529437795 40311413588721243794156693)
                    ·
                      refine ⟨1889597511971308302851095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40311413588721243794156693 1889597511971308302851095)
                      ·
                        rfl

theorem cell23_3679978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_3679978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3679978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3679978 prefixEnd_3679978 := by exact prefixLift 3679978
  have htrace : WordTrace (prefixWord ++ tailWord_3679978) baseStart_3679978 baseEnd_3679978 := by
    simpa [prefixWord, tailWord_3679978, baseEnd_3679978] using wordTrace_append hprefix tailTrace_3679978
  have hstable : (prefixWord ++ tailWord_3679978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3679978).length < 2 ^ (prefixWord ++ tailWord_3679978).sum := by decide
  have hdescent : baseEnd_3679978 < baseStart_3679978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3679978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680002 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_3680002 : Nat := 118140960795 + 3680002 * 2 ^ 59
def prefixEnd_3680002 : Nat := 4983230072969 + 3 ^ 40 * 3680002 * 2
def baseEnd_3680002 : Nat := 1889609835507016208950985

theorem tailTrace_3680002 : CollatzResearch.WordTrace tailWord_3680002 prefixEnd_3680002 1889609835507016208950985 := by
  unfold tailWord_3680002
  simp only [CollatzResearch.WordTrace]
  refine ⟨33555174903497180787430565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89480466409325815433148173 33555174903497180787430565)
  ·
    refine ⟨6291595294405721397643231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33555174903497180787430565 6291595294405721397643231)
    ·
      refine ⟨9437392941608582096464847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6291595294405721397643231 9437392941608582096464847)
      ·
        refine ⟨14156089412412873144697271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9437392941608582096464847 14156089412412873144697271)
        ·
          refine ⟨21234134118619309717045907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14156089412412873144697271 21234134118619309717045907)
          ·
            refine ⟨31851201177928964575568861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21234134118619309717045907 31851201177928964575568861)
            ·
              refine ⟨11944200441723361715838323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31851201177928964575568861 11944200441723361715838323)
              ·
                refine ⟨17916300662585042573757485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11944200441723361715838323 17916300662585042573757485)
                ·
                  refine ⟨6718612748469390965159057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17916300662585042573757485 6718612748469390965159057)
                  ·
                    refine ⟨5038959561352043223869293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6718612748469390965159057 5038959561352043223869293)
                    ·
                      refine ⟨1889609835507016208950985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5038959561352043223869293 1889609835507016208950985)
                      ·
                        rfl

theorem cell23_3680002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_3680002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680002 prefixEnd_3680002 := by exact prefixLift 3680002
  have htrace : WordTrace (prefixWord ++ tailWord_3680002) baseStart_3680002 baseEnd_3680002 := by
    simpa [prefixWord, tailWord_3680002, baseEnd_3680002] using wordTrace_append hprefix tailTrace_3680002
  have hstable : (prefixWord ++ tailWord_3680002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680002).length < 2 ^ (prefixWord ++ tailWord_3680002).sum := by decide
  have hdescent : baseEnd_3680002 < baseStart_3680002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680015 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 4, 1, 3]
def baseStart_3680015 : Nat := 118140960795 + 3680015 * 2 ^ 59
def prefixEnd_3680015 : Nat := 4983230072969 + 3 ^ 40 * 3680015 * 2
def baseEnd_3680015 : Nat := 1889616510755524658088425

theorem tailTrace_3680015 : CollatzResearch.WordTrace tailWord_3680015 prefixEnd_3680015 1889616510755524658088425 := by
  unfold tailWord_3680015
  simp only [CollatzResearch.WordTrace]
  refine ⟨134221173762941626369945499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89480782508627750913296999 134221173762941626369945499)
  ·
    refine ⟨201331760644412439554918249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134221173762941626369945499 201331760644412439554918249)
    ·
      refine ⟨150998820483309329666188687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201331760644412439554918249 150998820483309329666188687)
      ·
        refine ⟨226498230724963994499283031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150998820483309329666188687 226498230724963994499283031)
        ·
          refine ⟨339747346087445991748924547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226498230724963994499283031 339747346087445991748924547)
          ·
            refine ⟨509621019131168987623386821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339747346087445991748924547 509621019131168987623386821)
            ·
              refine ⟨95553941087094185179385029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 509621019131168987623386821 95553941087094185179385029)
              ·
                refine ⟨17916363953830159721134693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95553941087094185179385029 17916363953830159721134693)
                ·
                  refine ⟨3359318241343154947712755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17916363953830159721134693 3359318241343154947712755)
                  ·
                    refine ⟨5038977362014732421569133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3359318241343154947712755 5038977362014732421569133)
                    ·
                      refine ⟨1889616510755524658088425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5038977362014732421569133 1889616510755524658088425)
                      ·
                        rfl

theorem cell23_3680015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 1, 3].length) (baseStart_3680015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680015 prefixEnd_3680015 := by exact prefixLift 3680015
  have htrace : WordTrace (prefixWord ++ tailWord_3680015) baseStart_3680015 baseEnd_3680015 := by
    simpa [prefixWord, tailWord_3680015, baseEnd_3680015] using wordTrace_append hprefix tailTrace_3680015
  have hstable : (prefixWord ++ tailWord_3680015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680015).length < 2 ^ (prefixWord ++ tailWord_3680015).sum := by decide
  have hdescent : baseEnd_3680015 < baseStart_3680015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680033 : List Nat := [1, 2, 3, 2, 1, 5, 2, 2, 1, 2, 2]
def baseStart_3680033 : Nat := 118140960795 + 3680033 * 2 ^ 59
def prefixEnd_3680033 : Nat := 4983230072969 + 3 ^ 40 * 3680033 * 2
def baseEnd_3680033 : Nat := 1889625753407305587663343

theorem tailTrace_3680033 : CollatzResearch.WordTrace tailWord_3680033 prefixEnd_3680033 1889625753407305587663343 := by
  unfold tailWord_3680033
  simp only [CollatzResearch.WordTrace]
  refine ⟨134221830276876415444100753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89481220184584276962733835 134221830276876415444100753)
  ·
    refine ⟨100666372707657311583075565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134221830276876415444100753 100666372707657311583075565)
    ·
      refine ⟨37749889765371491843653337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100666372707657311583075565 37749889765371491843653337)
      ·
        refine ⟨28312417324028618882740003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37749889765371491843653337 28312417324028618882740003)
        ·
          refine ⟨42468625986042928324110005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28312417324028618882740003 42468625986042928324110005)
          ·
            refine ⟨3981433686191524530385313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42468625986042928324110005 3981433686191524530385313)
            ·
              refine ⟨2986075264643643397788985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3981433686191524530385313 2986075264643643397788985)
              ·
                refine ⟨2239556448482732548341739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2986075264643643397788985 2239556448482732548341739)
                ·
                  refine ⟨3359334672724098822512609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239556448482732548341739 3359334672724098822512609)
                  ·
                    refine ⟨2519501004543074116884457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3359334672724098822512609 2519501004543074116884457)
                    ·
                      refine ⟨1889625753407305587663343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2519501004543074116884457 1889625753407305587663343)
                      ·
                        rfl

theorem cell23_3680033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_3680033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680033 prefixEnd_3680033 := by exact prefixLift 3680033
  have htrace : WordTrace (prefixWord ++ tailWord_3680033) baseStart_3680033 baseEnd_3680033 := by
    simpa [prefixWord, tailWord_3680033, baseEnd_3680033] using wordTrace_append hprefix tailTrace_3680033
  have hstable : (prefixWord ++ tailWord_3680033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680033).length < 2 ^ (prefixWord ++ tailWord_3680033).sum := by decide
  have hdescent : baseEnd_3680033 < baseStart_3680033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680072 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 1, 4, 2]
def baseStart_3680072 : Nat := 118140960795 + 3680072 * 2 ^ 59
def prefixEnd_3680072 : Nat := 4983230072969 + 3 ^ 40 * 3680072 * 2
def baseEnd_3680072 : Nat := 1889645779152830935075663

theorem tailTrace_3680072 : CollatzResearch.WordTrace tailWord_3680072 prefixEnd_3680072 1889645779152830935075663 := by
  unfold tailWord_3680072
  simp only [CollatzResearch.WordTrace]
  refine ⟨67111626361867562552385235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89482168482490083403180313 67111626361867562552385235)
  ·
    refine ⟨100667439542801343828577853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67111626361867562552385235 100667439542801343828577853)
    ·
      refine ⟨37750289828550503935716695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100667439542801343828577853 37750289828550503935716695)
      ·
        refine ⟨56625434742825755903575043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37750289828550503935716695 56625434742825755903575043)
        ·
          refine ⟨84938152114238633855362565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56625434742825755903575043 84938152114238633855362565)
          ·
            refine ⟨15925903521419743847880481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84938152114238633855362565 15925903521419743847880481)
            ·
              refine ⟨11944427641064807885910361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15925903521419743847880481 11944427641064807885910361)
              ·
                refine ⟨8958320730798605914432771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11944427641064807885910361 8958320730798605914432771)
                ·
                  refine ⟨13437481096197908871649157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8958320730798605914432771 13437481096197908871649157)
                  ·
                    refine ⟨2519527705537107913434217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13437481096197908871649157 2519527705537107913434217)
                    ·
                      refine ⟨1889645779152830935075663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2519527705537107913434217 1889645779152830935075663)
                      ·
                        rfl

theorem cell23_3680072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_3680072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680072 prefixEnd_3680072 := by exact prefixLift 3680072
  have htrace : WordTrace (prefixWord ++ tailWord_3680072) baseStart_3680072 baseEnd_3680072 := by
    simpa [prefixWord, tailWord_3680072, baseEnd_3680072] using wordTrace_append hprefix tailTrace_3680072
  have hstable : (prefixWord ++ tailWord_3680072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680072).length < 2 ^ (prefixWord ++ tailWord_3680072).sum := by decide
  have hdescent : baseEnd_3680072 < baseStart_3680072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680085 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_3680085 : Nat := 118140960795 + 3680085 * 2 ^ 59
def prefixEnd_3680085 : Nat := 4983230072969 + 3 ^ 40 * 3680085 * 2
def baseEnd_3680085 : Nat := 1889652454401339384213103

theorem tailTrace_3680085 : CollatzResearch.WordTrace tailWord_3680085 prefixEnd_3680085 1889652454401339384213103 := by
  unfold tailWord_3680085
  simp only [CollatzResearch.WordTrace]
  refine ⟨134223726872688028324993709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89482484581792018883329139 134223726872688028324993709)
  ·
    refine ⟨50333897577258010621872641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134223726872688028324993709 50333897577258010621872641)
    ·
      refine ⟨37750423182943507966404481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50333897577258010621872641 37750423182943507966404481)
      ·
        refine ⟨28312817387207630974803361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37750423182943507966404481 28312817387207630974803361)
        ·
          refine ⟨21234613040405723231102521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28312817387207630974803361 21234613040405723231102521)
          ·
            refine ⟨15925959780304292423326891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21234613040405723231102521 15925959780304292423326891)
            ·
              refine ⟨23888939670456438634990337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15925959780304292423326891 23888939670456438634990337)
              ·
                refine ⟨17916704752842328976242753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23888939670456438634990337 17916704752842328976242753)
                ·
                  refine ⟨13437528564631746732182065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17916704752842328976242753 13437528564631746732182065)
                  ·
                    refine ⟨10078146423473810049136549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13437528564631746732182065 10078146423473810049136549)
                    ·
                      refine ⟨1889652454401339384213103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10078146423473810049136549 1889652454401339384213103)
                      ·
                        rfl

theorem cell23_3680085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_3680085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680085 prefixEnd_3680085 := by exact prefixLift 3680085
  have htrace : WordTrace (prefixWord ++ tailWord_3680085) baseStart_3680085 baseEnd_3680085 := by
    simpa [prefixWord, tailWord_3680085, baseEnd_3680085] using wordTrace_append hprefix tailTrace_3680085
  have hstable : (prefixWord ++ tailWord_3680085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680085).length < 2 ^ (prefixWord ++ tailWord_3680085).sum := by decide
  have hdescent : baseEnd_3680085 < baseStart_3680085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680095 : List Nat := [1, 1, 2, 3, 1, 5, 2, 1, 7]
def baseStart_3680095 : Nat := 118140960795 + 3680095 * 2 ^ 59
def prefixEnd_3680095 : Nat := 4983230072969 + 3 ^ 40 * 3680095 * 2
def baseEnd_3680095 : Nat := 209961954356431593898673

theorem tailTrace_3680095 : CollatzResearch.WordTrace tailWord_3680095 prefixEnd_3680095 209961954356431593898673 := by
  unfold tailWord_3680095
  simp only [CollatzResearch.WordTrace]
  refine ⟨134224091602651800032857739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89482727735101200021905159 134224091602651800032857739)
  ·
    refine ⟨201336137403977700049286609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134224091602651800032857739 201336137403977700049286609)
    ·
      refine ⟨151002103052983275036964957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201336137403977700049286609 151002103052983275036964957)
      ·
        refine ⟨56625788644868728138861859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151002103052983275036964957 56625788644868728138861859)
        ·
          refine ⟨84938682967303092208292789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56625788644868728138861859 84938682967303092208292789)
          ·
            refine ⟨7963001528184664894527449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84938682967303092208292789 7963001528184664894527449)
            ·
              refine ⟨5972251146138498670895587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7963001528184664894527449 5972251146138498670895587)
              ·
                refine ⟨8958376719207748006343381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5972251146138498670895587 8958376719207748006343381)
                ·
                  refine ⟨209961954356431593898673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8958376719207748006343381 209961954356431593898673)
                  ·
                    rfl

theorem cell23_3680095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 7].length) (baseStart_3680095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680095 prefixEnd_3680095 := by exact prefixLift 3680095
  have htrace : WordTrace (prefixWord ++ tailWord_3680095) baseStart_3680095 baseEnd_3680095 := by
    simpa [prefixWord, tailWord_3680095, baseEnd_3680095] using wordTrace_append hprefix tailTrace_3680095
  have hstable : (prefixWord ++ tailWord_3680095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680095).length < 2 ^ (prefixWord ++ tailWord_3680095).sum := by decide
  have hdescent : baseEnd_3680095 < baseStart_3680095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680125 : List Nat := [1, 4, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_3680125 : Nat := 118140960795 + 3680125 * 2 ^ 59
def prefixEnd_3680125 : Nat := 4983230072969 + 3 ^ 40 * 3680125 * 2
def baseEnd_3680125 : Nat := 629890997875839742570973

theorem tailTrace_3680125 : CollatzResearch.WordTrace tailWord_3680125 prefixEnd_3680125 629890997875839742570973 := by
  unfold tailWord_3680125
  simp only [CollatzResearch.WordTrace]
  refine ⟨134225185792543115156449829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89483457195028743437633219 134225185792543115156449829)
  ·
    refine ⟨25167222336101834091834343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134225185792543115156449829 25167222336101834091834343)
    ·
      refine ⟨37750833504152751137751515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25167222336101834091834343 37750833504152751137751515)
      ·
        refine ⟨56626250256229126706627273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37750833504152751137751515 56626250256229126706627273)
        ·
          refine ⟨42469687692171845029970455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56626250256229126706627273 42469687692171845029970455)
          ·
            refine ⟨63704531538257767544955683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42469687692171845029970455 63704531538257767544955683)
            ·
              refine ⟨95556797307386651317433525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63704531538257767544955683 95556797307386651317433525)
              ·
                refine ⟨8958449747567498561009393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95556797307386651317433525 8958449747567498561009393)
                ·
                  refine ⟨6718837310675623920757045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8958449747567498561009393 6718837310675623920757045)
                  ·
                    refine ⟨629890997875839742570973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6718837310675623920757045 629890997875839742570973)
                    ·
                      rfl

theorem cell23_3680125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_3680125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680125 prefixEnd_3680125 := by exact prefixLift 3680125
  have htrace : WordTrace (prefixWord ++ tailWord_3680125) baseStart_3680125 baseEnd_3680125 := by
    simpa [prefixWord, tailWord_3680125, baseEnd_3680125] using wordTrace_append hprefix tailTrace_3680125
  have hstable : (prefixWord ++ tailWord_3680125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680125).length < 2 ^ (prefixWord ++ tailWord_3680125).sum := by decide
  have hdescent : baseEnd_3680125 < baseStart_3680125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680145 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 4]
def baseStart_3680145 : Nat := 118140960795 + 3680145 * 2 ^ 59
def prefixEnd_3680145 : Nat := 4983230072969 + 3 ^ 40 * 3680145 * 2
def baseEnd_3680145 : Nat := 1889683263240609149462827

theorem tailTrace_3680145 : CollatzResearch.WordTrace tailWord_3680145 prefixEnd_3680145 1889683263240609149462827 := by
  unfold tailWord_3680145
  simp only [CollatzResearch.WordTrace]
  refine ⟨134225915252470658572177889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89483943501647105714785259 134225915252470658572177889)
  ·
    refine ⟨100669436439352993929133417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134225915252470658572177889 100669436439352993929133417)
    ·
      refine ⟨75502077329514745446850063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100669436439352993929133417 75502077329514745446850063)
      ·
        refine ⟨113253115994272118170275095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75502077329514745446850063 113253115994272118170275095)
        ·
          refine ⟨169879673991408177255412643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113253115994272118170275095 169879673991408177255412643)
          ·
            refine ⟨254819510987112265883118965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169879673991408177255412643 254819510987112265883118965)
            ·
              refine ⟨23889329155041774926542403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254819510987112265883118965 23889329155041774926542403)
              ·
                refine ⟨35833993732562662389813605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23889329155041774926542403 35833993732562662389813605)
                ·
                  refine ⟨6718873824855499198090051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35833993732562662389813605 6718873824855499198090051)
                  ·
                    refine ⟨10078310737283248797135077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6718873824855499198090051 10078310737283248797135077)
                    ·
                      refine ⟨1889683263240609149462827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10078310737283248797135077 1889683263240609149462827)
                      ·
                        rfl

theorem cell23_3680145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_3680145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680145 prefixEnd_3680145 := by exact prefixLift 3680145
  have htrace : WordTrace (prefixWord ++ tailWord_3680145) baseStart_3680145 baseEnd_3680145 := by
    simpa [prefixWord, tailWord_3680145, baseEnd_3680145] using wordTrace_append hprefix tailTrace_3680145
  have hstable : (prefixWord ++ tailWord_3680145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680145).length < 2 ^ (prefixWord ++ tailWord_3680145).sum := by decide
  have hdescent : baseEnd_3680145 < baseStart_3680145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680146 : List Nat := [3, 2, 3, 2, 1, 2, 3, 2, 5]
def baseStart_3680146 : Nat := 118140960795 + 3680146 * 2 ^ 59
def prefixEnd_3680146 : Nat := 4983230072969 + 3 ^ 40 * 3680146 * 2
def baseEnd_3680146 : Nat := 209964864080140405061147

theorem tailTrace_3680146 : CollatzResearch.WordTrace tailWord_3680146 prefixEnd_3680146 209964864080140405061147 := by
  unfold tailWord_3680146
  simp only [CollatzResearch.WordTrace]
  refine ⟨33556487931366758935741073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89483967816978023828642861 33556487931366758935741073)
  ·
    refine ⟨25167365948525069201805805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33556487931366758935741073 25167365948525069201805805)
    ·
      refine ⟨9437762230696900950677177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25167365948525069201805805 9437762230696900950677177)
      ·
        refine ⟨7078321673022675713007883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9437762230696900950677177 7078321673022675713007883)
        ·
          refine ⟨10617482509534013569511825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7078321673022675713007883 10617482509534013569511825)
          ·
            refine ⟨7963111882150510177133869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10617482509534013569511825 7963111882150510177133869)
            ·
              refine ⟨2986166955806441316425201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7963111882150510177133869 2986166955806441316425201)
              ·
                refine ⟨2239625216854830987318901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2986166955806441316425201 2239625216854830987318901)
                ·
                  refine ⟨209964864080140405061147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2239625216854830987318901 209964864080140405061147)
                  ·
                    rfl

theorem cell23_3680146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_3680146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680146 prefixEnd_3680146 := by exact prefixLift 3680146
  have htrace : WordTrace (prefixWord ++ tailWord_3680146) baseStart_3680146 baseEnd_3680146 := by
    simpa [prefixWord, tailWord_3680146, baseEnd_3680146] using wordTrace_append hprefix tailTrace_3680146
  have hstable : (prefixWord ++ tailWord_3680146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680146).length < 2 ^ (prefixWord ++ tailWord_3680146).sum := by decide
  have hdescent : baseEnd_3680146 < baseStart_3680146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680165 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 3, 4, 3]
def baseStart_3680165 : Nat := 118140960795 + 3680165 * 2 ^ 59
def prefixEnd_3680165 : Nat := 4983230072969 + 3 ^ 40 * 3680165 * 2
def baseEnd_3680165 : Nat := 1889693532853699071212735

theorem tailTrace_3680165 : CollatzResearch.WordTrace tailWord_3680165 prefixEnd_3680165 1889693532853699071212735 := by
  unfold tailWord_3680165
  simp only [CollatzResearch.WordTrace]
  refine ⟨134226644712398201987905949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89484429808265467991937299 134226644712398201987905949)
  ·
    refine ⟨50334991767149325745464731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134226644712398201987905949 50334991767149325745464731)
    ·
      refine ⟨75502487650723988618197097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50334991767149325745464731 75502487650723988618197097)
      ·
        refine ⟨56626865738042991463647823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75502487650723988618197097 56626865738042991463647823)
        ·
          refine ⟨84940298607064487195471735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56626865738042991463647823 84940298607064487195471735)
          ·
            refine ⟨127410447910596730793207603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84940298607064487195471735 127410447910596730793207603)
            ·
              refine ⟨191115671865895096189811405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127410447910596730793207603 191115671865895096189811405)
              ·
                refine ⟨71668376949710661071179277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191115671865895096189811405 71668376949710661071179277)
                ·
                  refine ⟨26875641356141497901692229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71668376949710661071179277 26875641356141497901692229)
                  ·
                    refine ⟨5039182754276530856567293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26875641356141497901692229 5039182754276530856567293)
                    ·
                      refine ⟨1889693532853699071212735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5039182754276530856567293 1889693532853699071212735)
                      ·
                        rfl

theorem cell23_3680165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_3680165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680165 prefixEnd_3680165 := by exact prefixLift 3680165
  have htrace : WordTrace (prefixWord ++ tailWord_3680165) baseStart_3680165 baseEnd_3680165 := by
    simpa [prefixWord, tailWord_3680165, baseEnd_3680165] using wordTrace_append hprefix tailTrace_3680165
  have hstable : (prefixWord ++ tailWord_3680165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680165).length < 2 ^ (prefixWord ++ tailWord_3680165).sum := by decide
  have hdescent : baseEnd_3680165 < baseStart_3680165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680215 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 5, 5]
def baseStart_3680215 : Nat := 118140960795 + 3680215 * 2 ^ 59
def prefixEnd_3680215 : Nat := 4983230072969 + 3 ^ 40 * 3680215 * 2
def baseEnd_3680215 : Nat := 629906402295474625195835

theorem tailTrace_3680215 : CollatzResearch.WordTrace tailWord_3680215 prefixEnd_3680215 629906402295474625195835 := by
  unfold tailWord_3680215
  simp only [CollatzResearch.WordTrace]
  refine ⟨134228468362217060527226099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89485645574811373684817399 134228468362217060527226099)
  ·
    refine ⟨201342702543325590790839149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134228468362217060527226099 201342702543325590790839149)
    ·
      refine ⟨75503513453747096546564681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201342702543325590790839149 75503513453747096546564681)
      ·
        refine ⟨56627635090310322409923511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75503513453747096546564681 56627635090310322409923511)
        ·
          refine ⟨84941452635465483614885267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56627635090310322409923511 84941452635465483614885267)
          ·
            refine ⟨127412178953198225422327901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84941452635465483614885267 127412178953198225422327901)
            ·
              refine ⟨47779567107449334533372963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127412178953198225422327901 47779567107449334533372963)
              ·
                refine ⟨71669350661174001800059445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47779567107449334533372963 71669350661174001800059445)
                ·
                  refine ⟨6719001624485062668755573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71669350661174001800059445 6719001624485062668755573)
                  ·
                    refine ⟨629906402295474625195835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6719001624485062668755573 629906402295474625195835)
                    ·
                      rfl

theorem cell23_3680215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_3680215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680215 prefixEnd_3680215 := by exact prefixLift 3680215
  have htrace : WordTrace (prefixWord ++ tailWord_3680215) baseStart_3680215 baseEnd_3680215 := by
    simpa [prefixWord, tailWord_3680215, baseEnd_3680215] using wordTrace_append hprefix tailTrace_3680215
  have hstable : (prefixWord ++ tailWord_3680215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680215).length < 2 ^ (prefixWord ++ tailWord_3680215).sum := by decide
  have hdescent : baseEnd_3680215 < baseStart_3680215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680232 : List Nat := [2, 1, 4, 1, 1, 1, 1, 6, 1, 5]
def baseStart_3680232 : Nat := 118140960795 + 3680232 * 2 ^ 59
def prefixEnd_3680232 : Nat := 4983230072969 + 3 ^ 40 * 3680232 * 2
def baseEnd_3680232 : Nat := 629909312019183436358309

theorem tailTrace_3680232 : CollatzResearch.WordTrace tailWord_3680232 prefixEnd_3680232 629909312019183436358309 := by
  unfold tailWord_3680232
  simp only [CollatzResearch.WordTrace]
  refine ⟨67114544201577736215297475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89486058935436981620396633 67114544201577736215297475)
  ·
    refine ⟨100671816302366604322946213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67114544201577736215297475 100671816302366604322946213)
    ·
      refine ⟨18875965556693738310552415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100671816302366604322946213 18875965556693738310552415)
      ·
        refine ⟨28313948335040607465828623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18875965556693738310552415 28313948335040607465828623)
        ·
          refine ⟨42470922502560911198742935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28313948335040607465828623 42470922502560911198742935)
          ·
            refine ⟨63706383753841366798114403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42470922502560911198742935 63706383753841366798114403)
            ·
              refine ⟨95559575630762050197171605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63706383753841366798114403 95559575630762050197171605)
              ·
                refine ⟨4479355107691971102992419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95559575630762050197171605 4479355107691971102992419)
                ·
                  refine ⟨6719032661537956654488629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4479355107691971102992419 6719032661537956654488629)
                  ·
                    refine ⟨629909312019183436358309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6719032661537956654488629 629909312019183436358309)
                    ·
                      rfl

theorem cell23_3680232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_3680232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680232 prefixEnd_3680232 := by exact prefixLift 3680232
  have htrace : WordTrace (prefixWord ++ tailWord_3680232) baseStart_3680232 baseEnd_3680232 := by
    simpa [prefixWord, tailWord_3680232, baseEnd_3680232] using wordTrace_append hprefix tailTrace_3680232
  have hstable : (prefixWord ++ tailWord_3680232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680232).length < 2 ^ (prefixWord ++ tailWord_3680232).sum := by decide
  have hdescent : baseEnd_3680232 < baseStart_3680232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680249 : List Nat := [1, 2, 1, 3, 1, 4, 4, 1, 1, 5]
def baseStart_3680249 : Nat := 118140960795 + 3680249 * 2 ^ 59
def prefixEnd_3680249 : Nat := 4983230072969 + 3 ^ 40 * 3680249 * 2
def baseEnd_3680249 : Nat := 629912221742892247520783

theorem tailTrace_3680249 : CollatzResearch.WordTrace tailWord_3680249 prefixEnd_3680249 629912221742892247520783 := by
  unfold tailWord_3680249
  simp only [CollatzResearch.WordTrace]
  refine ⟨134229708444093884333963801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89486472296062589555975867 134229708444093884333963801)
  ·
    refine ⟨100672281333070413250472851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134229708444093884333963801 100672281333070413250472851)
    ·
      refine ⟨151008421999605619875709277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100672281333070413250472851 151008421999605619875709277)
      ·
        refine ⟨56628158249852107453390979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151008421999605619875709277 56628158249852107453390979)
        ·
          refine ⟨84942237374778161180086469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56628158249852107453390979 84942237374778161180086469)
          ·
            refine ⟨15926669507770905221266213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84942237374778161180086469 15926669507770905221266213)
            ·
              refine ⟨2986250532707044728987415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15926669507770905221266213 2986250532707044728987415)
              ·
                refine ⟨4479375799060567093481123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2986250532707044728987415 4479375799060567093481123)
                ·
                  refine ⟨6719063698590850640221685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4479375799060567093481123 6719063698590850640221685)
                  ·
                    refine ⟨629912221742892247520783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6719063698590850640221685 629912221742892247520783)
                    ·
                      rfl

theorem cell23_3680249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 1, 5].length) (baseStart_3680249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680249 prefixEnd_3680249 := by exact prefixLift 3680249
  have htrace : WordTrace (prefixWord ++ tailWord_3680249) baseStart_3680249 baseEnd_3680249 := by
    simpa [prefixWord, tailWord_3680249, baseEnd_3680249] using wordTrace_append hprefix tailTrace_3680249
  have hstable : (prefixWord ++ tailWord_3680249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680249).length < 2 ^ (prefixWord ++ tailWord_3680249).sum := by decide
  have hdescent : baseEnd_3680249 < baseStart_3680249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680255 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 5]
def baseStart_3680255 : Nat := 118140960795 + 3680255 * 2 ^ 59
def prefixEnd_3680255 : Nat := 4983230072969 + 3 ^ 40 * 3680255 * 2
def baseEnd_3680255 : Nat := 1889739746112603719087321

theorem tailTrace_3680255 : CollatzResearch.WordTrace tailWord_3680255 prefixEnd_3680255 1889739746112603719087321 := by
  unfold tailWord_3680255
  simp only [CollatzResearch.WordTrace]
  refine ⟨134229927282072147358682219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89486618188048098239121479 134229927282072147358682219)
  ·
    refine ⟨201344890923108221038023329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134229927282072147358682219 201344890923108221038023329)
    ·
      refine ⟨151008668192331165778517497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201344890923108221038023329 151008668192331165778517497)
      ·
        refine ⟨113256501144248374333888123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151008668192331165778517497 113256501144248374333888123)
        ·
          refine ⟨169884751716372561500832185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113256501144248374333888123 169884751716372561500832185)
          ·
            refine ⟨127413563787279421125624139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169884751716372561500832185 127413563787279421125624139)
            ·
              refine ⟨191120345680919131688436209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127413563787279421125624139 191120345680919131688436209)
              ·
                refine ⟨143340259260689348766327157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191120345680919131688436209 143340259260689348766327157)
                ·
                  refine ⟨13438149305689626446843171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143340259260689348766327157 13438149305689626446843171)
                  ·
                    refine ⟨20157223958534439670264757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13438149305689626446843171 20157223958534439670264757)
                    ·
                      refine ⟨1889739746112603719087321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20157223958534439670264757 1889739746112603719087321)
                      ·
                        rfl

theorem cell23_3680255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_3680255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680255 prefixEnd_3680255 := by exact prefixLift 3680255
  have htrace : WordTrace (prefixWord ++ tailWord_3680255) baseStart_3680255 baseEnd_3680255 := by
    simpa [prefixWord, tailWord_3680255, baseEnd_3680255] using wordTrace_append hprefix tailTrace_3680255
  have hstable : (prefixWord ++ tailWord_3680255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680255).length < 2 ^ (prefixWord ++ tailWord_3680255).sum := by decide
  have hdescent : baseEnd_3680255 < baseStart_3680255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680265 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 2, 6, 4]
def baseStart_3680265 : Nat := 118140960795 + 3680265 * 2 ^ 59
def prefixEnd_3680265 : Nat := 4983230072969 + 3 ^ 40 * 3680265 * 2
def baseEnd_3680265 : Nat := 1889744880919148679962275

theorem tailTrace_3680265 : CollatzResearch.WordTrace tailWord_3680265 prefixEnd_3680265 1889744880919148679962275 := by
  unfold tailWord_3680265
  simp only [CollatzResearch.WordTrace]
  refine ⟨134230292012035919066546249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89486861341357279377697499 134230292012035919066546249)
  ·
    refine ⟨100672719009026939299909687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134230292012035919066546249 100672719009026939299909687)
    ·
      refine ⟨151009078513540408949864531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100672719009026939299909687 151009078513540408949864531)
      ·
        refine ⟨226513617770310613424796797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151009078513540408949864531 226513617770310613424796797)
        ·
          refine ⟨84942606663866480034298799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226513617770310613424796797 84942606663866480034298799)
          ·
            refine ⟨127413909995799720051448199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84942606663866480034298799 127413909995799720051448199)
            ·
              refine ⟨191120864993699580077172299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127413909995799720051448199 191120864993699580077172299)
              ·
                refine ⟨286681297490549370115758449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191120864993699580077172299 286681297490549370115758449)
                ·
                  refine ⟨215010973117912027586818837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286681297490549370115758449 215010973117912027586818837)
                  ·
                    refine ⟨10078639364902126293132133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 215010973117912027586818837 10078639364902126293132133)
                    ·
                      refine ⟨1889744880919148679962275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10078639364902126293132133 1889744880919148679962275)
                      ·
                        rfl

theorem cell23_3680265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_3680265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680265 prefixEnd_3680265 := by exact prefixLift 3680265
  have htrace : WordTrace (prefixWord ++ tailWord_3680265) baseStart_3680265 baseEnd_3680265 := by
    simpa [prefixWord, tailWord_3680265, baseEnd_3680265] using wordTrace_append hprefix tailTrace_3680265
  have hstable : (prefixWord ++ tailWord_3680265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680265).length < 2 ^ (prefixWord ++ tailWord_3680265).sum := by decide
  have hdescent : baseEnd_3680265 < baseStart_3680265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680282 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6]
def baseStart_3680282 : Nat := 118140960795 + 3680282 * 2 ^ 59
def prefixEnd_3680282 : Nat := 4983230072969 + 3 ^ 40 * 3680282 * 2
def baseEnd_3680282 : Nat := 1889753610090275113449697

theorem tailTrace_3680282 : CollatzResearch.WordTrace tailWord_3680282 prefixEnd_3680282 1889753610090275113449697 := by
  unfold tailWord_3680282
  simp only [CollatzResearch.WordTrace]
  refine ⟨33557728013243582742478775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89487274701982887313276733 33557728013243582742478775)
  ·
    refine ⟨50336592019865374113718163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33557728013243582742478775 50336592019865374113718163)
    ·
      refine ⟨75504888029798061170577245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50336592019865374113718163 75504888029798061170577245)
      ·
        refine ⟨28314333011174272938966467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75504888029798061170577245 28314333011174272938966467)
        ·
          refine ⟨42471499516761409408449701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28314333011174272938966467 42471499516761409408449701)
          ·
            refine ⟨7963406159392764264084319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42471499516761409408449701 7963406159392764264084319)
            ·
              refine ⟨11945109239089146396126479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7963406159392764264084319 11945109239089146396126479)
              ·
                refine ⟨17917663858633719594189719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11945109239089146396126479 17917663858633719594189719)
                ·
                  refine ⟨26876495787950579391284579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17917663858633719594189719 26876495787950579391284579)
                  ·
                    refine ⟨40314743681925869086926869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26876495787950579391284579 40314743681925869086926869)
                    ·
                      refine ⟨1889753610090275113449697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40314743681925869086926869 1889753610090275113449697)
                      ·
                        rfl

theorem cell23_3680282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_3680282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680282 prefixEnd_3680282 := by exact prefixLift 3680282
  have htrace : WordTrace (prefixWord ++ tailWord_3680282) baseStart_3680282 baseEnd_3680282 := by
    simpa [prefixWord, tailWord_3680282, baseEnd_3680282] using wordTrace_append hprefix tailTrace_3680282
  have hstable : (prefixWord ++ tailWord_3680282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680282).length < 2 ^ (prefixWord ++ tailWord_3680282).sum := by decide
  have hdescent : baseEnd_3680282 < baseStart_3680282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680319 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 4, 1, 3]
def baseStart_3680319 : Nat := 118140960795 + 3680319 * 2 ^ 59
def prefixEnd_3680319 : Nat := 4983230072969 + 3 ^ 40 * 3680319 * 2
def baseEnd_3680319 : Nat := 1889772608874491468687027

theorem tailTrace_3680319 : CollatzResearch.WordTrace tailWord_3680319 prefixEnd_3680319 1889772608874491468687027 := by
  unfold tailWord_3680319
  simp only [CollatzResearch.WordTrace]
  refine ⟨134232261553840286289012011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89488174369226857526008007 134232261553840286289012011)
  ·
    refine ⟨201348392330760429433518017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134232261553840286289012011 201348392330760429433518017)
    ·
      refine ⟨151011294248070322075138513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201348392330760429433518017 151011294248070322075138513)
      ·
        refine ⟨113258470686052741556353885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151011294248070322075138513 113258470686052741556353885)
        ·
          refine ⟨42471926507269778083632707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113258470686052741556353885 42471926507269778083632707)
          ·
            refine ⟨63707889760904667125449061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42471926507269778083632707 63707889760904667125449061)
            ·
              refine ⟨11945229330169625086021699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63707889760904667125449061 11945229330169625086021699)
              ·
                refine ⟨17917843995254437629032549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11945229330169625086021699 17917843995254437629032549)
                ·
                  refine ⟨3359595749110207055443603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17917843995254437629032549 3359595749110207055443603)
                  ·
                    refine ⟨5039393623665310583165405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3359595749110207055443603 5039393623665310583165405)
                    ·
                      refine ⟨1889772608874491468687027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5039393623665310583165405 1889772608874491468687027)
                      ·
                        rfl

theorem cell23_3680319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 1, 3].length) (baseStart_3680319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680319 prefixEnd_3680319 := by exact prefixLift 3680319
  have htrace : WordTrace (prefixWord ++ tailWord_3680319) baseStart_3680319 baseEnd_3680319 := by
    simpa [prefixWord, tailWord_3680319, baseEnd_3680319] using wordTrace_append hprefix tailTrace_3680319
  have hstable : (prefixWord ++ tailWord_3680319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680319).length < 2 ^ (prefixWord ++ tailWord_3680319).sum := by decide
  have hdescent : baseEnd_3680319 < baseStart_3680319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680320 : List Nat := [2, 1, 1, 2, 2, 5, 3, 2, 1, 2, 2]
def baseStart_3680320 : Nat := 118140960795 + 3680320 * 2 ^ 59
def prefixEnd_3680320 : Nat := 4983230072969 + 3 ^ 40 * 3680320 * 2
def baseEnd_3680320 : Nat := 1889773122355145964774523

theorem tailTrace_3680320 : CollatzResearch.WordTrace tailWord_3680320 prefixEnd_3680320 1889773122355145964774523 := by
  unfold tailWord_3680320
  simp only [CollatzResearch.WordTrace]
  refine ⟨67116149013418331729899207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89488198684557775639865609 67116149013418331729899207)
  ·
    refine ⟨100674223520127497594848811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67116149013418331729899207 100674223520127497594848811)
    ·
      refine ⟨151011335280191246392273217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100674223520127497594848811 151011335280191246392273217)
      ·
        refine ⟨113258501460143434794204913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151011335280191246392273217 113258501460143434794204913)
        ·
          refine ⟨84943876095107576095653685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113258501460143434794204913 84943876095107576095653685)
          ·
            refine ⟨7963488383916335258967533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84943876095107576095653685 7963488383916335258967533)
            ·
              refine ⟨2986308143968625722112825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7963488383916335258967533 2986308143968625722112825)
              ·
                refine ⟨2239731107976469291584619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2986308143968625722112825 2239731107976469291584619)
                ·
                  refine ⟨3359596661964703937376929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239731107976469291584619 3359596661964703937376929)
                  ·
                    refine ⟨2519697496473527953032697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3359596661964703937376929 2519697496473527953032697)
                    ·
                      refine ⟨1889773122355145964774523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2519697496473527953032697 1889773122355145964774523)
                      ·
                        rfl

theorem cell23_3680320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 1, 2, 2].length) (baseStart_3680320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680320 prefixEnd_3680320 := by exact prefixLift 3680320
  have htrace : WordTrace (prefixWord ++ tailWord_3680320) baseStart_3680320 baseEnd_3680320 := by
    simpa [prefixWord, tailWord_3680320, baseEnd_3680320] using wordTrace_append hprefix tailTrace_3680320
  have hstable : (prefixWord ++ tailWord_3680320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680320).length < 2 ^ (prefixWord ++ tailWord_3680320).sum := by decide
  have hdescent : baseEnd_3680320 < baseStart_3680320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680329 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 3, 3, 2]
def baseStart_3680329 : Nat := 118140960795 + 3680329 * 2 ^ 59
def prefixEnd_3680329 : Nat := 4983230072969 + 3 ^ 40 * 3680329 * 2
def baseEnd_3680329 : Nat := 1889777743681036429561981

theorem tailTrace_3680329 : CollatzResearch.WordTrace tailWord_3680329 prefixEnd_3680329 1889777743681036429561981 := by
  unfold tailWord_3680329
  simp only [CollatzResearch.WordTrace]
  refine ⟨134232626283804057996876041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89488417522536038664584027 134232626283804057996876041)
  ·
    refine ⟨100674469712853043497657031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134232626283804057996876041 100674469712853043497657031)
    ·
      refine ⟨151011704569279565246485547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100674469712853043497657031 151011704569279565246485547)
      ·
        refine ⟨226517556853919347869728321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151011704569279565246485547 226517556853919347869728321)
        ·
          refine ⟨169888167640439510902296241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226517556853919347869728321 169888167640439510902296241)
          ·
            refine ⟨127416125730329633176722181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169888167640439510902296241 127416125730329633176722181)
            ·
              refine ⟨23890523574436806220635409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127416125730329633176722181 23890523574436806220635409)
              ·
                refine ⟨17917892680827604665476557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23890523574436806220635409 17917892680827604665476557)
                ·
                  refine ⟨6719209755310351749553709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17917892680827604665476557 6719209755310351749553709)
                  ·
                    refine ⟨2519703658241381906082641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6719209755310351749553709 2519703658241381906082641)
                    ·
                      refine ⟨1889777743681036429561981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2519703658241381906082641 1889777743681036429561981)
                      ·
                        rfl

theorem cell23_3680329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 3, 2].length) (baseStart_3680329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680329 prefixEnd_3680329 := by exact prefixLift 3680329
  have htrace : WordTrace (prefixWord ++ tailWord_3680329) baseStart_3680329 baseEnd_3680329 := by
    simpa [prefixWord, tailWord_3680329, baseEnd_3680329] using wordTrace_append hprefix tailTrace_3680329
  have hstable : (prefixWord ++ tailWord_3680329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680329).length < 2 ^ (prefixWord ++ tailWord_3680329).sum := by decide
  have hdescent : baseEnd_3680329 < baseStart_3680329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680389 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 2, 2, 4]
def baseStart_3680389 : Nat := 118140960795 + 3680389 * 2 ^ 59
def prefixEnd_3680389 : Nat := 4983230072969 + 3 ^ 40 * 3680389 * 2
def baseEnd_3680389 : Nat := 1889808552520306194811705

theorem tailTrace_3680389 : CollatzResearch.WordTrace tailWord_3680389 prefixEnd_3680389 1889808552520306194811705 := by
  unfold tailWord_3680389
  simp only [CollatzResearch.WordTrace]
  refine ⟨134234814663586688244060221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89489876442391125496040147 134234814663586688244060221)
  ·
    refine ⟨50338055498845008091522583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134234814663586688244060221 50338055498845008091522583)
    ·
      refine ⟨75507083248267512137283875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50338055498845008091522583 75507083248267512137283875)
      ·
        refine ⟨113260624872401268205925813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75507083248267512137283875 113260624872401268205925813)
        ·
          refine ⟨10618183581787618894305545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113260624872401268205925813 10618183581787618894305545)
          ·
            refine ⟨7963637686340714170729159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10618183581787618894305545 7963637686340714170729159)
            ·
              refine ⟨11945456529511071256093739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7963637686340714170729159 11945456529511071256093739)
              ·
                refine ⟨17918184794266606884140609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11945456529511071256093739 17918184794266606884140609)
                ·
                  refine ⟨13438638595699955163105457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17918184794266606884140609 13438638595699955163105457)
                  ·
                    refine ⟨10078978946774966372329093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13438638595699955163105457 10078978946774966372329093)
                    ·
                      refine ⟨1889808552520306194811705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10078978946774966372329093 1889808552520306194811705)
                      ·
                        rfl

theorem cell23_3680389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_3680389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680389 prefixEnd_3680389 := by exact prefixLift 3680389
  have htrace : WordTrace (prefixWord ++ tailWord_3680389) baseStart_3680389 baseEnd_3680389 := by
    simpa [prefixWord, tailWord_3680389, baseEnd_3680389] using wordTrace_append hprefix tailTrace_3680389
  have hstable : (prefixWord ++ tailWord_3680389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680389).length < 2 ^ (prefixWord ++ tailWord_3680389).sum := by decide
  have hdescent : baseEnd_3680389 < baseStart_3680389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680414 : List Nat := [4, 3, 1, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_3680414 : Nat := 118140960795 + 3680414 * 2 ^ 59
def prefixEnd_3680414 : Nat := 4983230072969 + 3 ^ 40 * 3680414 * 2
def baseEnd_3680414 : Nat := 1889821389536668596999091

theorem tailTrace_3680414 : CollatzResearch.WordTrace tailWord_3680414 prefixEnd_3680414 1889821389536668596999091 := by
  unfold tailWord_3680414
  simp only [CollatzResearch.WordTrace]
  refine ⟨16779465811062014689215037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89490484325664078342480197 16779465811062014689215037)
  ·
    refine ⟨6292299679148255508455639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16779465811062014689215037 6292299679148255508455639)
    ·
      refine ⟨9438449518722383262683459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6292299679148255508455639 9438449518722383262683459)
      ·
        refine ⟨14157674278083574894025189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9438449518722383262683459 14157674278083574894025189)
        ·
          refine ⟨2654563927140670292629723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14157674278083574894025189 2654563927140670292629723)
          ·
            refine ⟨3981845890711005438944585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654563927140670292629723 3981845890711005438944585)
            ·
              refine ⟨2986384418033254079208439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3981845890711005438944585 2986384418033254079208439)
              ·
                refine ⟨4479576627049881118812659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2986384418033254079208439 4479576627049881118812659)
                ·
                  refine ⟨6719364940574821678218989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4479576627049881118812659 6719364940574821678218989)
                  ·
                    refine ⟨2519761852715558129332121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6719364940574821678218989 2519761852715558129332121)
                    ·
                      refine ⟨1889821389536668596999091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2519761852715558129332121 1889821389536668596999091)
                      ·
                        rfl

theorem cell23_3680414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_3680414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680414 prefixEnd_3680414 := by exact prefixLift 3680414
  have htrace : WordTrace (prefixWord ++ tailWord_3680414) baseStart_3680414 baseEnd_3680414 := by
    simpa [prefixWord, tailWord_3680414, baseEnd_3680414] using wordTrace_append hprefix tailTrace_3680414
  have hstable : (prefixWord ++ tailWord_3680414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680414).length < 2 ^ (prefixWord ++ tailWord_3680414).sum := by decide
  have hdescent : baseEnd_3680414 < baseStart_3680414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680416 : List Nat := [2, 1, 1, 4, 2, 3, 2, 3, 5]
def baseStart_3680416 : Nat := 118140960795 + 3680416 * 2 ^ 59
def prefixEnd_3680416 : Nat := 4983230072969 + 3 ^ 40 * 3680416 * 2
def baseEnd_3680416 : Nat := 209980268499775287686009

theorem tailTrace_3680416 : CollatzResearch.WordTrace tailWord_3680416 prefixEnd_3680416 209980268499775287686009 := by
  unfold tailWord_3680416
  simp only [CollatzResearch.WordTrace]
  refine ⟨67117899717244435927646551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89490532956325914570195401 67117899717244435927646551)
  ·
    refine ⟨100676849575866653891469827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67117899717244435927646551 100676849575866653891469827)
    ·
      refine ⟨151015274363799980837204741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100676849575866653891469827 151015274363799980837204741)
      ·
        refine ⟨28315363943212496406975889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151015274363799980837204741 28315363943212496406975889)
        ·
          refine ⟨21236522957409372305231917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28315363943212496406975889 21236522957409372305231917)
          ·
            refine ⟨7963696109028514614461969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21236522957409372305231917 7963696109028514614461969)
            ·
              refine ⟨5972772081771385960846477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7963696109028514614461969 5972772081771385960846477)
              ·
                refine ⟨2239789530664269735317429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5972772081771385960846477 2239789530664269735317429)
                ·
                  refine ⟨209980268499775287686009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2239789530664269735317429 209980268499775287686009)
                  ·
                    rfl

theorem cell23_3680416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 5].length) (baseStart_3680416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680416 prefixEnd_3680416 := by exact prefixLift 3680416
  have htrace : WordTrace (prefixWord ++ tailWord_3680416) baseStart_3680416 baseEnd_3680416 := by
    simpa [prefixWord, tailWord_3680416, baseEnd_3680416] using wordTrace_append hprefix tailTrace_3680416
  have hstable : (prefixWord ++ tailWord_3680416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680416).length < 2 ^ (prefixWord ++ tailWord_3680416).sum := by decide
  have hdescent : baseEnd_3680416 < baseStart_3680416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680432 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 4]
def baseStart_3680432 : Nat := 118140960795 + 3680432 * 2 ^ 59
def prefixEnd_3680432 : Nat := 4983230072969 + 3 ^ 40 * 3680432 * 2
def baseEnd_3680432 : Nat := 1889830632188449526574007

theorem tailTrace_3680432 : CollatzResearch.WordTrace tailWord_3680432 prefixEnd_3680432 1889830632188449526574007 := by
  unfold tailWord_3680432
  simp only [CollatzResearch.WordTrace]
  refine ⟨67118191501215453293937775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89490922001620604391917033 67118191501215453293937775)
  ·
    refine ⟨100677287251823179940906663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67118191501215453293937775 100677287251823179940906663)
    ·
      refine ⟨151015930877734769911359995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100677287251823179940906663 151015930877734769911359995)
      ·
        refine ⟨226523896316602154867039993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151015930877734769911359995 226523896316602154867039993)
        ·
          refine ⟨169892922237451616150279995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226523896316602154867039993 169892922237451616150279995)
          ·
            refine ⟨254839383356177424225419993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169892922237451616150279995 254839383356177424225419993)
            ·
              refine ⟨191129537517133068169064995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254839383356177424225419993 191129537517133068169064995)
              ·
                refine ⟨286694306275699602253597493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191129537517133068169064995 286694306275699602253597493)
                ·
                  refine ⟨26877591213346837711274765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 286694306275699602253597493 26877591213346837711274765)
                  ·
                    refine ⟨10079096705005064141728037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26877591213346837711274765 10079096705005064141728037)
                    ·
                      refine ⟨1889830632188449526574007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10079096705005064141728037 1889830632188449526574007)
                      ·
                        rfl

theorem cell23_3680432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_3680432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680432 prefixEnd_3680432 := by exact prefixLift 3680432
  have htrace : WordTrace (prefixWord ++ tailWord_3680432) baseStart_3680432 baseEnd_3680432 := by
    simpa [prefixWord, tailWord_3680432, baseEnd_3680432] using wordTrace_append hprefix tailTrace_3680432
  have hstable : (prefixWord ++ tailWord_3680432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680432).length < 2 ^ (prefixWord ++ tailWord_3680432).sum := by decide
  have hdescent : baseEnd_3680432 < baseStart_3680432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680459 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 3, 4]
def baseStart_3680459 : Nat := 118140960795 + 3680459 * 2 ^ 59
def prefixEnd_3680459 : Nat := 4983230072969 + 3 ^ 40 * 3680459 * 2
def baseEnd_3680459 : Nat := 629948165388706973645461

theorem tailTrace_3680459 : CollatzResearch.WordTrace tailWord_3680459 prefixEnd_3680459 629948165388706973645461 := by
  unfold tailWord_3680459
  simp only [CollatzResearch.WordTrace]
  refine ⟨134237367773333090199108431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89491578515555393466072287 134237367773333090199108431)
  ·
    refine ⟨201356051659999635298662647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134237367773333090199108431 201356051659999635298662647)
    ·
      refine ⟨302034077489999452947993971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201356051659999635298662647 302034077489999452947993971)
      ·
        refine ⟨453051116234999179421990957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302034077489999452947993971 453051116234999179421990957)
        ·
          refine ⟨169894168588124692283246609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453051116234999179421990957 169894168588124692283246609)
          ·
            refine ⟨127420626441093519212434957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169894168588124692283246609 127420626441093519212434957)
            ·
              refine ⟨47782734915410069704663109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127420626441093519212434957 47782734915410069704663109)
              ·
                refine ⟨8959262796639388069624333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47782734915410069704663109 8959262796639388069624333)
                ·
                  refine ⟨3359723548739770526109125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8959262796639388069624333 3359723548739770526109125)
                  ·
                    refine ⟨629948165388706973645461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3359723548739770526109125 629948165388706973645461)
                    ·
                      rfl

theorem cell23_3680459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 3, 4].length) (baseStart_3680459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680459 prefixEnd_3680459 := by exact prefixLift 3680459
  have htrace : WordTrace (prefixWord ++ tailWord_3680459) baseStart_3680459 baseEnd_3680459 := by
    simpa [prefixWord, tailWord_3680459, baseEnd_3680459] using wordTrace_append hprefix tailTrace_3680459
  have hstable : (prefixWord ++ tailWord_3680459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680459).length < 2 ^ (prefixWord ++ tailWord_3680459).sum := by decide
  have hdescent : baseEnd_3680459 < baseStart_3680459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680483 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3680483 : Nat := 118140960795 + 3680483 * 2 ^ 59
def prefixEnd_3680483 : Nat := 4983230072969 + 3 ^ 40 * 3680483 * 2
def baseEnd_3680483 : Nat := 1889856819701828827036273

theorem tailTrace_3680483 : CollatzResearch.WordTrace tailWord_3680483 prefixEnd_3680483 1889856819701828827036273 := by
  unfold tailWord_3680483
  simp only [CollatzResearch.WordTrace]
  refine ⟨134238243125246142297982103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89492162083497428198654735 134238243125246142297982103)
  ·
    refine ⟨201357364687869213446973155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134238243125246142297982103 201357364687869213446973155)
    ·
      refine ⟨302036047031803820170459733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201357364687869213446973155 302036047031803820170459733)
      ·
        refine ⟨3539484926153951017622575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 302036047031803820170459733 3539484926153951017622575)
        ·
          refine ⟨5309227389230926526433863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3539484926153951017622575 5309227389230926526433863)
          ·
            refine ⟨7963841083846389789650795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5309227389230926526433863 7963841083846389789650795)
            ·
              refine ⟨11945761625769584684476193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7963841083846389789650795 11945761625769584684476193)
              ·
                refine ⟨8959321219327188513357145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11945761625769584684476193 8959321219327188513357145)
                ·
                  refine ⟨6719490914495391385017859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8959321219327188513357145 6719490914495391385017859)
                  ·
                    refine ⟨10079236371743087077526789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6719490914495391385017859 10079236371743087077526789)
                    ·
                      refine ⟨1889856819701828827036273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10079236371743087077526789 1889856819701828827036273)
                      ·
                        rfl

theorem cell23_3680483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3680483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680483 prefixEnd_3680483 := by exact prefixLift 3680483
  have htrace : WordTrace (prefixWord ++ tailWord_3680483) baseStart_3680483 baseEnd_3680483 := by
    simpa [prefixWord, tailWord_3680483, baseEnd_3680483] using wordTrace_append hprefix tailTrace_3680483
  have hstable : (prefixWord ++ tailWord_3680483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680483).length < 2 ^ (prefixWord ++ tailWord_3680483).sum := by decide
  have hdescent : baseEnd_3680483 < baseStart_3680483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680506 : List Nat := [3, 1, 1, 1, 1, 5, 4, 1, 6]
def baseStart_3680506 : Nat := 118140960795 + 3680506 * 2 ^ 59
def prefixEnd_3680506 : Nat := 4983230072969 + 3 ^ 40 * 3680506 * 2
def baseEnd_3680506 : Nat := 209985403306320248560963

theorem tailTrace_3680506 : CollatzResearch.WordTrace tailWord_3680506 prefixEnd_3680506 209985403306320248560963 := by
  unfold tailWord_3680506
  simp only [CollatzResearch.WordTrace]
  refine ⟨33559770501040704306517343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89492721336108544817379581 33559770501040704306517343)
  ·
    refine ⟨50339655751561056459776015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33559770501040704306517343 50339655751561056459776015)
    ·
      refine ⟨75509483627341584689664023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50339655751561056459776015 75509483627341584689664023)
      ·
        refine ⟨113264225441012377034496035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75509483627341584689664023 113264225441012377034496035)
        ·
          refine ⟨169896338161518565551744053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113264225441012377034496035 169896338161518565551744053)
          ·
            refine ⟨15927781702642365520476005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169896338161518565551744053 15927781702642365520476005)
            ·
              refine ⟨2986459069245443535089251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15927781702642365520476005 2986459069245443535089251)
              ·
                refine ⟨4479688603868165302633877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2986459069245443535089251 4479688603868165302633877)
                ·
                  refine ⟨209985403306320248560963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4479688603868165302633877 209985403306320248560963)
                  ·
                    rfl

theorem cell23_3680506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 6].length) (baseStart_3680506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680506 prefixEnd_3680506 := by exact prefixLift 3680506
  have htrace : WordTrace (prefixWord ++ tailWord_3680506) baseStart_3680506 baseEnd_3680506 := by
    simpa [prefixWord, tailWord_3680506, baseEnd_3680506] using wordTrace_append hprefix tailTrace_3680506
  have hstable : (prefixWord ++ tailWord_3680506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680506).length < 2 ^ (prefixWord ++ tailWord_3680506).sum := by decide
  have hdescent : baseEnd_3680506 < baseStart_3680506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680543 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 2, 3, 2]
def baseStart_3680543 : Nat := 118140960795 + 3680543 * 2 ^ 59
def prefixEnd_3680543 : Nat := 4983230072969 + 3 ^ 40 * 3680543 * 2
def baseEnd_3680543 : Nat := 1889887628541098592285997

theorem tailTrace_3680543 : CollatzResearch.WordTrace tailWord_3680543 prefixEnd_3680543 1889887628541098592285997 := by
  unfold tailWord_3680543
  simp only [CollatzResearch.WordTrace]
  refine ⟨134240431505028772545166283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89493621003352515030110855 134240431505028772545166283)
  ·
    refine ⟨201360647257543158817749425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134240431505028772545166283 201360647257543158817749425)
    ·
      refine ⟨151020485443157369113312069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201360647257543158817749425 151020485443157369113312069)
      ·
        refine ⟨28316341020592006708746013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151020485443157369113312069 28316341020592006708746013)
        ·
          refine ⟨10618627882722002515779755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28316341020592006708746013 10618627882722002515779755)
          ·
            refine ⟨15927941824083003773669633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10618627882722002515779755 15927941824083003773669633)
            ·
              refine ⟨11945956368062252830252225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15927941824083003773669633 11945956368062252830252225)
              ·
                refine ⟨8959467276046689622689169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11945956368062252830252225 8959467276046689622689169)
                ·
                  refine ⟨6719600457035017217016877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8959467276046689622689169 6719600457035017217016877)
                  ·
                    refine ⟨2519850171388131456381329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6719600457035017217016877 2519850171388131456381329)
                    ·
                      refine ⟨1889887628541098592285997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2519850171388131456381329 1889887628541098592285997)
                      ·
                        rfl

theorem cell23_3680543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_3680543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680543 prefixEnd_3680543 := by exact prefixLift 3680543
  have htrace : WordTrace (prefixWord ++ tailWord_3680543) baseStart_3680543 baseEnd_3680543 := by
    simpa [prefixWord, tailWord_3680543, baseEnd_3680543] using wordTrace_append hprefix tailTrace_3680543
  have hstable : (prefixWord ++ tailWord_3680543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680543).length < 2 ^ (prefixWord ++ tailWord_3680543).sum := by decide
  have hdescent : baseEnd_3680543 < baseStart_3680543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680559 : List Nat := [1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 5]
def baseStart_3680559 : Nat := 118140960795 + 3680559 * 2 ^ 59
def prefixEnd_3680559 : Nat := 4983230072969 + 3 ^ 40 * 3680559 * 2
def baseEnd_3680559 : Nat := 1889895844231570529685923

theorem tailTrace_3680559 : CollatzResearch.WordTrace tailWord_3680559 prefixEnd_3680559 1889895844231570529685923 := by
  unfold tailWord_3680559
  simp only [CollatzResearch.WordTrace]
  refine ⟨134241015072970807277748731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89494010048647204851832487 134241015072970807277748731)
  ·
    refine ⟨201361522609456210916623097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134241015072970807277748731 201361522609456210916623097)
    ·
      refine ⟨151021141957092158187467323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201361522609456210916623097 151021141957092158187467323)
      ·
        refine ⟨226531712935638237281200985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151021141957092158187467323 226531712935638237281200985)
        ·
          refine ⟨169898784701728677960900739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226531712935638237281200985 169898784701728677960900739)
          ·
            refine ⟨254848177052593016941351109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169898784701728677960900739 254848177052593016941351109)
            ·
              refine ⟨47784033197361190676503333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254848177052593016941351109 47784033197361190676503333)
              ·
                refine ⟨8959506224505223251844375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47784033197361190676503333 8959506224505223251844375)
                ·
                  refine ⟨13439259336757834877766563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8959506224505223251844375 13439259336757834877766563)
                  ·
                    refine ⟨20158889005136752316649845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13439259336757834877766563 20158889005136752316649845)
                    ·
                      refine ⟨1889895844231570529685923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20158889005136752316649845 1889895844231570529685923)
                      ·
                        rfl

theorem cell23_3680559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 5].length) (baseStart_3680559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680559 prefixEnd_3680559 := by exact prefixLift 3680559
  have htrace : WordTrace (prefixWord ++ tailWord_3680559) baseStart_3680559 baseEnd_3680559 := by
    simpa [prefixWord, tailWord_3680559, baseEnd_3680559] using wordTrace_append hprefix tailTrace_3680559
  have hstable : (prefixWord ++ tailWord_3680559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680559).length < 2 ^ (prefixWord ++ tailWord_3680559).sum := by decide
  have hdescent : baseEnd_3680559 < baseStart_3680559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680577 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_3680577 : Nat := 118140960795 + 3680577 * 2 ^ 59
def prefixEnd_3680577 : Nat := 4983230072969 + 3 ^ 40 * 3680577 * 2
def baseEnd_3680577 : Nat := 1889905086883351459260841

theorem tailTrace_3680577 : CollatzResearch.WordTrace tailWord_3680577 prefixEnd_3680577 1889905086883351459260841 := by
  unfold tailWord_3680577
  simp only [CollatzResearch.WordTrace]
  refine ⟨134241671586905596351903985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89494447724603730901269323 134241671586905596351903985)
  ·
    refine ⟨100681253690179197263927989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134241671586905596351903985 100681253690179197263927989)
    ·
      refine ⟨9438867533454299743493249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100681253690179197263927989 9438867533454299743493249)
      ·
        refine ⟨7079150650090724807619937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9438867533454299743493249 7079150650090724807619937)
        ·
          refine ⟨5309362987568043605714953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7079150650090724807619937 5309362987568043605714953)
          ·
            refine ⟨3982022240676032704286215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5309362987568043605714953 3982022240676032704286215)
            ·
              refine ⟨5973033361014049056429323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3982022240676032704286215 5973033361014049056429323)
              ·
                refine ⟨8959550041521073584643985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5973033361014049056429323 8959550041521073584643985)
                ·
                  refine ⟨6719662531140805188482989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8959550041521073584643985 6719662531140805188482989)
                  ·
                    refine ⟨2519873449177801945681121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6719662531140805188482989 2519873449177801945681121)
                    ·
                      refine ⟨1889905086883351459260841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2519873449177801945681121 1889905086883351459260841)
                      ·
                        rfl

theorem cell23_3680577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_3680577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680577 prefixEnd_3680577 := by exact prefixLift 3680577
  have htrace : WordTrace (prefixWord ++ tailWord_3680577) baseStart_3680577 baseEnd_3680577 := by
    simpa [prefixWord, tailWord_3680577, baseEnd_3680577] using wordTrace_append hprefix tailTrace_3680577
  have hstable : (prefixWord ++ tailWord_3680577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680577).length < 2 ^ (prefixWord ++ tailWord_3680577).sum := by decide
  have hdescent : baseEnd_3680577 < baseStart_3680577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680593 : List Nat := [1, 2, 2, 1, 4, 3, 1, 3, 1, 2, 3]
def baseStart_3680593 : Nat := 118140960795 + 3680593 * 2 ^ 59
def prefixEnd_3680593 : Nat := 4983230072969 + 3 ^ 40 * 3680593 * 2
def baseEnd_3680593 : Nat := 1889913302573823396660767

theorem tailTrace_3680593 : CollatzResearch.WordTrace tailWord_3680593 prefixEnd_3680593 1889913302573823396660767 := by
  unfold tailWord_3680593
  simp only [CollatzResearch.WordTrace]
  refine ⟨134242255154847631084486433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89494836769898420722990955 134242255154847631084486433)
  ·
    refine ⟨100681691366135723313364825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134242255154847631084486433 100681691366135723313364825)
    ·
      refine ⟨75511268524601792485023619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100681691366135723313364825 75511268524601792485023619)
      ·
        refine ⟨113266902786902688727535429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75511268524601792485023619 113266902786902688727535429)
        ·
          refine ⟨21237544272544254136412893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113266902786902688727535429 21237544272544254136412893)
          ·
            refine ⟨7964079102204095301154835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21237544272544254136412893 7964079102204095301154835)
            ·
              refine ⟨11946118653306142951732253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7964079102204095301154835 11946118653306142951732253)
              ·
                refine ⟨4479794494989803606899595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11946118653306142951732253 4479794494989803606899595)
                ·
                  refine ⟨6719691742484705410349393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4479794494989803606899595 6719691742484705410349393)
                  ·
                    refine ⟨5039768806863529057762045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6719691742484705410349393 5039768806863529057762045)
                    ·
                      refine ⟨1889913302573823396660767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5039768806863529057762045 1889913302573823396660767)
                      ·
                        rfl

theorem cell23_3680593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_3680593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680593 prefixEnd_3680593 := by exact prefixLift 3680593
  have htrace : WordTrace (prefixWord ++ tailWord_3680593) baseStart_3680593 baseEnd_3680593 := by
    simpa [prefixWord, tailWord_3680593, baseEnd_3680593] using wordTrace_append hprefix tailTrace_3680593
  have hstable : (prefixWord ++ tailWord_3680593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680593).length < 2 ^ (prefixWord ++ tailWord_3680593).sum := by decide
  have hdescent : baseEnd_3680593 < baseStart_3680593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680620 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 1, 2, 4]
def baseStart_3680620 : Nat := 118140960795 + 3680620 * 2 ^ 59
def prefixEnd_3680620 : Nat := 4983230072969 + 3 ^ 40 * 3680620 * 2
def baseEnd_3680620 : Nat := 1889927166551494791023143

theorem tailTrace_3680620 : CollatzResearch.WordTrace tailWord_3680620 prefixEnd_3680620 1889927166551494791023143 := by
  unfold tailWord_3680620
  simp only [CollatzResearch.WordTrace]
  refine ⟨67121619962874907347859657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89495493283833209797146209 67121619962874907347859657)
  ·
    refine ⟨50341214972156180510894743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67121619962874907347859657 50341214972156180510894743)
    ·
      refine ⟨75511822458234270766342115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50341214972156180510894743 75511822458234270766342115)
      ·
        refine ⟨113267733687351406149513173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75511822458234270766342115 113267733687351406149513173)
        ·
          refine ⟨2654712508297298581629215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 113267733687351406149513173 2654712508297298581629215)
          ·
            refine ⟨3982068762445947872443823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654712508297298581629215 3982068762445947872443823)
            ·
              refine ⟨5973103143668921808665735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3982068762445947872443823 5973103143668921808665735)
              ·
                refine ⟨8959654715503382712998603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5973103143668921808665735 8959654715503382712998603)
                ·
                  refine ⟨13439482073255074069497905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8959654715503382712998603 13439482073255074069497905)
                  ·
                    refine ⟨10079611554941305552123429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13439482073255074069497905 10079611554941305552123429)
                    ·
                      refine ⟨1889927166551494791023143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10079611554941305552123429 1889927166551494791023143)
                      ·
                        rfl

theorem cell23_3680620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 1, 2, 4].length) (baseStart_3680620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680620 prefixEnd_3680620 := by exact prefixLift 3680620
  have htrace : WordTrace (prefixWord ++ tailWord_3680620) baseStart_3680620 baseEnd_3680620 := by
    simpa [prefixWord, tailWord_3680620, baseEnd_3680620] using wordTrace_append hprefix tailTrace_3680620
  have hstable : (prefixWord ++ tailWord_3680620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680620).length < 2 ^ (prefixWord ++ tailWord_3680620).sum := by decide
  have hdescent : baseEnd_3680620 < baseStart_3680620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680676 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_3680676 : Nat := 118140960795 + 3680676 * 2 ^ 59
def prefixEnd_3680676 : Nat := 4983230072969 + 3 ^ 40 * 3680676 * 2
def baseEnd_3680676 : Nat := 1889955921468146571922885

theorem tailTrace_3680676 : CollatzResearch.WordTrace tailWord_3680676 prefixEnd_3680676 1889955921468146571922885 := by
  unfold tailWord_3680676
  simp only [CollatzResearch.WordTrace]
  refine ⟨67122641206773468129878941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89496854942364624173171921 67122641206773468129878941)
  ·
    refine ⟨25170990452540050548704603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67122641206773468129878941 25170990452540050548704603)
    ·
      refine ⟨37756485678810075823056905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25170990452540050548704603 37756485678810075823056905)
      ·
        refine ⟨28317364259107556867292679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37756485678810075823056905 28317364259107556867292679)
        ·
          refine ⟨42476046388661335300939019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28317364259107556867292679 42476046388661335300939019)
          ·
            refine ⟨63714069582992002951408529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42476046388661335300939019 63714069582992002951408529)
            ·
              refine ⟨47785552187244002213556397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63714069582992002951408529 47785552187244002213556397)
              ·
                refine ⟨17919582070216500830083649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47785552187244002213556397 17919582070216500830083649)
                ·
                  refine ⟨13439686552662375622562737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17919582070216500830083649 13439686552662375622562737)
                  ·
                    refine ⟨10079764914496781716922053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13439686552662375622562737 10079764914496781716922053)
                    ·
                      refine ⟨1889955921468146571922885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10079764914496781716922053 1889955921468146571922885)
                      ·
                        rfl

theorem cell23_3680676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_3680676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680676 prefixEnd_3680676 := by exact prefixLift 3680676
  have htrace : WordTrace (prefixWord ++ tailWord_3680676) baseStart_3680676 baseEnd_3680676 := by
    simpa [prefixWord, tailWord_3680676, baseEnd_3680676] using wordTrace_append hprefix tailTrace_3680676
  have hstable : (prefixWord ++ tailWord_3680676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680676).length < 2 ^ (prefixWord ++ tailWord_3680676).sum := by decide
  have hdescent : baseEnd_3680676 < baseStart_3680676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680696 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 4, 3, 3]
def baseStart_3680696 : Nat := 118140960795 + 3680696 * 2 ^ 59
def prefixEnd_3680696 : Nat := 4983230072969 + 3 ^ 40 * 3680696 * 2
def baseEnd_3680696 : Nat := 1889966191081236493672793

theorem tailTrace_3680696 : CollatzResearch.WordTrace tailWord_3680696 prefixEnd_3680696 1889966191081236493672793 := by
  unfold tailWord_3680696
  simp only [CollatzResearch.WordTrace]
  refine ⟨67123005936737239837742971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89497341248982986450323961 67123005936737239837742971)
  ·
    refine ⟨100684508905105859756614457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67123005936737239837742971 100684508905105859756614457)
    ·
      refine ⟨75513381678829394817460843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100684508905105859756614457 75513381678829394817460843)
      ·
        refine ⟨113270072518244092226191265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75513381678829394817460843 113270072518244092226191265)
        ·
          refine ⟨84952554388683069169643449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113270072518244092226191265 84952554388683069169643449)
          ·
            refine ⟨63714415791512301877232587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84952554388683069169643449 63714415791512301877232587)
            ·
              refine ⟨95571623687268452815848881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63714415791512301877232587 95571623687268452815848881)
              ·
                refine ⟨71678717765451339611886661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95571623687268452815848881 71678717765451339611886661)
                ·
                  refine ⟨13439759581022126177228749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71678717765451339611886661 13439759581022126177228749)
                  ·
                    refine ⟨5039909842883297316460781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13439759581022126177228749 5039909842883297316460781)
                    ·
                      refine ⟨1889966191081236493672793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5039909842883297316460781 1889966191081236493672793)
                      ·
                        rfl

theorem cell23_3680696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_3680696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680696 prefixEnd_3680696 := by exact prefixLift 3680696
  have htrace : WordTrace (prefixWord ++ tailWord_3680696) baseStart_3680696 baseEnd_3680696 := by
    simpa [prefixWord, tailWord_3680696, baseEnd_3680696] using wordTrace_append hprefix tailTrace_3680696
  have hstable : (prefixWord ++ tailWord_3680696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680696).length < 2 ^ (prefixWord ++ tailWord_3680696).sum := by decide
  have hdescent : baseEnd_3680696 < baseStart_3680696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680736 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 4]
def baseStart_3680736 : Nat := 118140960795 + 3680736 * 2 ^ 59
def prefixEnd_3680736 : Nat := 4983230072969 + 3 ^ 40 * 3680736 * 2
def baseEnd_3680736 : Nat := 1889986730307416337172609

theorem tailTrace_3680736 : CollatzResearch.WordTrace tailWord_3680736 prefixEnd_3680736 1889986730307416337172609 := by
  unfold tailWord_3680736
  simp only [CollatzResearch.WordTrace]
  refine ⟨67123735396664783253471031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89498313862219711004628041 67123735396664783253471031)
  ·
    refine ⟨100685603094997174880206547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67123735396664783253471031 100685603094997174880206547)
    ·
      refine ⟨151028404642495762320309821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100685603094997174880206547 151028404642495762320309821)
      ·
        refine ⟨56635651740935910870116183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151028404642495762320309821 56635651740935910870116183)
        ·
          refine ⟨84953477611403866305174275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56635651740935910870116183 84953477611403866305174275)
          ·
            refine ⟨127430216417105799457761413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84953477611403866305174275 127430216417105799457761413)
            ·
              refine ⟨23893165578207337398330265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127430216417105799457761413 23893165578207337398330265)
              ·
                refine ⟨17919874183655503048747699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23893165578207337398330265 17919874183655503048747699)
                ·
                  refine ⟨26879811275483254573121549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17919874183655503048747699 26879811275483254573121549)
                  ·
                    refine ⟨10079929228306220464920581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26879811275483254573121549 10079929228306220464920581)
                    ·
                      refine ⟨1889986730307416337172609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10079929228306220464920581 1889986730307416337172609)
                      ·
                        rfl

theorem cell23_3680736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_3680736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680736 prefixEnd_3680736 := by exact prefixLift 3680736
  have htrace : WordTrace (prefixWord ++ tailWord_3680736) baseStart_3680736 baseEnd_3680736 := by
    simpa [prefixWord, tailWord_3680736, baseEnd_3680736] using wordTrace_append hprefix tailTrace_3680736
  have hstable : (prefixWord ++ tailWord_3680736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680736).length < 2 ^ (prefixWord ++ tailWord_3680736).sum := by decide
  have hdescent : baseEnd_3680736 < baseStart_3680736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680750 : List Nat := [4, 1, 2, 1, 2, 4, 1, 1, 2, 5]
def baseStart_3680750 : Nat := 118140960795 + 3680750 * 2 ^ 59
def prefixEnd_3680750 : Nat := 4983230072969 + 3 ^ 40 * 3680750 * 2
def baseEnd_3680750 : Nat := 629997973012193094132515

theorem tailTrace_3680750 : CollatzResearch.WordTrace tailWord_3680750 prefixEnd_3680750 629997973012193094132515 := by
  unfold tailWord_3680750
  simp only [CollatzResearch.WordTrace]
  refine ⟨16780997676909855862243963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89498654276852564598634469 16780997676909855862243963)
  ·
    refine ⟨25171496515364783793365945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16780997676909855862243963 25171496515364783793365945)
    ·
      refine ⟨18878622386523587845024459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25171496515364783793365945 18878622386523587845024459)
      ·
        refine ⟨28317933579785381767536689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18878622386523587845024459 28317933579785381767536689)
        ·
          refine ⟨21238450184839036325652517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28317933579785381767536689 21238450184839036325652517)
          ·
            refine ⟨3982209409657319311059847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21238450184839036325652517 3982209409657319311059847)
            ·
              refine ⟨5973314114485978966589771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3982209409657319311059847 5973314114485978966589771)
              ·
                refine ⟨8959971171728968449884657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5973314114485978966589771 8959971171728968449884657)
                ·
                  refine ⟨6719978378796726337413493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8959971171728968449884657 6719978378796726337413493)
                  ·
                    refine ⟨629997973012193094132515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6719978378796726337413493 629997973012193094132515)
                    ·
                      rfl

theorem cell23_3680750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_3680750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680750 prefixEnd_3680750 := by exact prefixLift 3680750
  have htrace : WordTrace (prefixWord ++ tailWord_3680750) baseStart_3680750 baseEnd_3680750 := by
    simpa [prefixWord, tailWord_3680750, baseEnd_3680750] using wordTrace_append hprefix tailTrace_3680750
  have hstable : (prefixWord ++ tailWord_3680750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680750).length < 2 ^ (prefixWord ++ tailWord_3680750).sum := by decide
  have hdescent : baseEnd_3680750 < baseStart_3680750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680753 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 1, 6, 2]
def baseStart_3680753 : Nat := 118140960795 + 3680753 * 2 ^ 59
def prefixEnd_3680753 : Nat := 4983230072969 + 3 ^ 40 * 3680753 * 2
def baseEnd_3680753 : Nat := 1889995459478542770660031

theorem tailTrace_3680753 : CollatzResearch.WordTrace tailWord_3680753 prefixEnd_3680753 1889995459478542770660031 := by
  unfold tailWord_3680753
  simp only [CollatzResearch.WordTrace]
  refine ⟨134248090834267978410310913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89498727222845318940207275 134248090834267978410310913)
  ·
    refine ⟨100686068125700983807733185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134248090834267978410310913 100686068125700983807733185)
    ·
      refine ⟨75514551094275737855799889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100686068125700983807733185 75514551094275737855799889)
      ·
        refine ⟨56635913320706803391849917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75514551094275737855799889 56635913320706803391849917)
        ·
          refine ⟨21238467495265051271943719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56635913320706803391849917 21238467495265051271943719)
          ·
            refine ⟨31857701242897576907915579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21238467495265051271943719 31857701242897576907915579)
            ·
              refine ⟨47786551864346365361873369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31857701242897576907915579 47786551864346365361873369)
              ·
                refine ⟨35839913898259774021405027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47786551864346365361873369 35839913898259774021405027)
                ·
                  refine ⟨53759870847389661032107541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35839913898259774021405027 53759870847389661032107541)
                  ·
                    refine ⟨2519993945971390360880041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53759870847389661032107541 2519993945971390360880041)
                    ·
                      refine ⟨1889995459478542770660031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2519993945971390360880041 1889995459478542770660031)
                      ·
                        rfl

theorem cell23_3680753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_3680753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680753 prefixEnd_3680753 := by exact prefixLift 3680753
  have htrace : WordTrace (prefixWord ++ tailWord_3680753) baseStart_3680753 baseEnd_3680753 := by
    simpa [prefixWord, tailWord_3680753, baseEnd_3680753] using wordTrace_append hprefix tailTrace_3680753
  have hstable : (prefixWord ++ tailWord_3680753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680753).length < 2 ^ (prefixWord ++ tailWord_3680753).sum := by decide
  have hdescent : baseEnd_3680753 < baseStart_3680753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680773 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 2, 2, 3]
def baseStart_3680773 : Nat := 118140960795 + 3680773 * 2 ^ 59
def prefixEnd_3680773 : Nat := 4983230072969 + 3 ^ 40 * 3680773 * 2
def baseEnd_3680773 : Nat := 1890005729091632692409939

theorem tailTrace_3680773 : CollatzResearch.WordTrace tailWord_3680773 prefixEnd_3680773 1890005729091632692409939 := by
  unfold tailWord_3680773
  simp only [CollatzResearch.WordTrace]
  refine ⟨134248820294195521826038973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89499213529463681217359315 134248820294195521826038973)
  ·
    refine ⟨50343307610323320684764615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134248820294195521826038973 50343307610323320684764615)
    ·
      refine ⟨75514961415484981027146923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50343307610323320684764615 75514961415484981027146923)
      ·
        refine ⟨113272442123227471540720385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75514961415484981027146923 113272442123227471540720385)
        ·
          refine ⟨84954331592420603655540289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113272442123227471540720385 84954331592420603655540289)
          ·
            refine ⟨63715748694315452741655217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84954331592420603655540289 63715748694315452741655217)
            ·
              refine ⟨47786811520736589556241413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63715748694315452741655217 47786811520736589556241413)
              ·
                refine ⟨8960027160138110541795265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47786811520736589556241413 8960027160138110541795265)
                ·
                  refine ⟨6720020370103582906346449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8960027160138110541795265 6720020370103582906346449)
                  ·
                    refine ⟨5040015277577687179759837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6720020370103582906346449 5040015277577687179759837)
                    ·
                      refine ⟨1890005729091632692409939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5040015277577687179759837 1890005729091632692409939)
                      ·
                        rfl

theorem cell23_3680773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_3680773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680773 prefixEnd_3680773 := by exact prefixLift 3680773
  have htrace : WordTrace (prefixWord ++ tailWord_3680773) baseStart_3680773 baseEnd_3680773 := by
    simpa [prefixWord, tailWord_3680773, baseEnd_3680773] using wordTrace_append hprefix tailTrace_3680773
  have hstable : (prefixWord ++ tailWord_3680773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680773).length < 2 ^ (prefixWord ++ tailWord_3680773).sum := by decide
  have hdescent : baseEnd_3680773 < baseStart_3680773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680780 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 3, 4]
def baseStart_3680780 : Nat := 118140960795 + 3680780 * 2 ^ 59
def prefixEnd_3680780 : Nat := 4983230072969 + 3 ^ 40 * 3680780 * 2
def baseEnd_3680780 : Nat := 630003107818738055007469

theorem tailTrace_3680780 : CollatzResearch.WordTrace tailWord_3680780 prefixEnd_3680780 630003107818738055007469 := by
  unfold tailWord_3680780
  simp only [CollatzResearch.WordTrace]
  refine ⟨67124537802585081010771897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89499383736780108014362529 67124537802585081010771897)
  ·
    refine ⟨50343403351938810758078923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67124537802585081010771897 50343403351938810758078923)
    ·
      refine ⟨75515105027908216137118385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50343403351938810758078923 75515105027908216137118385)
      ·
        refine ⟨56636328770931162102838789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75515105027908216137118385 56636328770931162102838789)
        ·
          refine ⟨10619311644549592894282273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56636328770931162102838789 10619311644549592894282273)
          ·
            refine ⟨7964483733412194670711705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10619311644549592894282273 7964483733412194670711705)
            ·
              refine ⟨5973362800059146003033779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7964483733412194670711705 5973362800059146003033779)
              ·
                refine ⟨8960044200088719004550669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5973362800059146003033779 8960044200088719004550669)
                ·
                  refine ⟨3360016575033269626706501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8960044200088719004550669 3360016575033269626706501)
                  ·
                    refine ⟨630003107818738055007469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3360016575033269626706501 630003107818738055007469)
                    ·
                      rfl

theorem cell23_3680780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_3680780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680780 prefixEnd_3680780 := by exact prefixLift 3680780
  have htrace : WordTrace (prefixWord ++ tailWord_3680780) baseStart_3680780 baseEnd_3680780 := by
    simpa [prefixWord, tailWord_3680780, baseEnd_3680780] using wordTrace_append hprefix tailTrace_3680780
  have hstable : (prefixWord ++ tailWord_3680780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680780).length < 2 ^ (prefixWord ++ tailWord_3680780).sum := by decide
  have hdescent : baseEnd_3680780 < baseStart_3680780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680823 : List Nat := [1, 1, 3, 1, 2, 3, 1, 5, 1, 5]
def baseStart_3680823 : Nat := 118140960795 + 3680823 * 2 ^ 59
def prefixEnd_3680823 : Nat := 4983230072969 + 3 ^ 40 * 3680823 * 2
def baseEnd_3680823 : Nat := 630010467708119165594903

theorem tailTrace_3680823 : CollatzResearch.WordTrace tailWord_3680823 prefixEnd_3680823 630010467708119165594903 := by
  unfold tailWord_3680823
  simp only [CollatzResearch.WordTrace]
  refine ⟨134250643944014380365359123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89500429296009586910239415 134250643944014380365359123)
  ·
    refine ⟨201375965916021570548038685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134250643944014380365359123 201375965916021570548038685)
    ·
      refine ⟨75515987218508088955514507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201375965916021570548038685 75515987218508088955514507)
      ·
        refine ⟨113273980827762133433271761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75515987218508088955514507 113273980827762133433271761)
        ·
          refine ⟨84955485620821600074953821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113273980827762133433271761 84955485620821600074953821)
          ·
            refine ⟨31858307107808100028107683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84955485620821600074953821 31858307107808100028107683)
            ·
              refine ⟨47787460661712150042161525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31858307107808100028107683 47787460661712150042161525)
              ·
                refine ⟨4480074437035514066452643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47787460661712150042161525 4480074437035514066452643)
                ·
                  refine ⟨6720111655553271099678965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4480074437035514066452643 6720111655553271099678965)
                  ·
                    refine ⟨630010467708119165594903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6720111655553271099678965 630010467708119165594903)
                    ·
                      rfl

theorem cell23_3680823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_3680823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680823 prefixEnd_3680823 := by exact prefixLift 3680823
  have htrace : WordTrace (prefixWord ++ tailWord_3680823) baseStart_3680823 baseEnd_3680823 := by
    simpa [prefixWord, tailWord_3680823, baseEnd_3680823] using wordTrace_append hprefix tailTrace_3680823
  have hstable : (prefixWord ++ tailWord_3680823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680823).length < 2 ^ (prefixWord ++ tailWord_3680823).sum := by decide
  have hdescent : baseEnd_3680823 < baseStart_3680823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680837 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 3, 1, 3]
def baseStart_3680837 : Nat := 118140960795 + 3680837 * 2 ^ 59
def prefixEnd_3680837 : Nat := 4983230072969 + 3 ^ 40 * 3680837 * 2
def baseEnd_3680837 : Nat := 1890038591853520442009645

theorem tailTrace_3680837 : CollatzResearch.WordTrace tailWord_3680837 prefixEnd_3680837 1890038591853520442009645 := by
  unfold tailWord_3680837
  simp only [CollatzResearch.WordTrace]
  refine ⟨134251154565963660756368765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89500769710642440504245843 134251154565963660756368765)
  ·
    refine ⟨50344182962236372783638287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134251154565963660756368765 50344182962236372783638287)
    ·
      refine ⟨75516274443354559175457431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50344182962236372783638287 75516274443354559175457431)
      ·
        refine ⟨113274411665031838763186147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75516274443354559175457431 113274411665031838763186147)
        ·
          refine ⟨169911617497547758144779221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113274411665031838763186147 169911617497547758144779221)
          ·
            refine ⟨3982303535098775581518263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 169911617497547758144779221 3982303535098775581518263)
            ·
              refine ⟨5973455302648163372277395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3982303535098775581518263 5973455302648163372277395)
              ·
                refine ⟨8960182953972245058416093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5973455302648163372277395 8960182953972245058416093)
                ·
                  refine ⟨3360068607739591896906035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8960182953972245058416093 3360068607739591896906035)
                  ·
                    refine ⟨5040102911609387845359053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3360068607739591896906035 5040102911609387845359053)
                    ·
                      refine ⟨1890038591853520442009645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5040102911609387845359053 1890038591853520442009645)
                      ·
                        rfl

theorem cell23_3680837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_3680837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680837 prefixEnd_3680837 := by exact prefixLift 3680837
  have htrace : WordTrace (prefixWord ++ tailWord_3680837) baseStart_3680837 baseEnd_3680837 := by
    simpa [prefixWord, tailWord_3680837, baseEnd_3680837] using wordTrace_append hprefix tailTrace_3680837
  have hstable : (prefixWord ++ tailWord_3680837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680837).length < 2 ^ (prefixWord ++ tailWord_3680837).sum := by decide
  have hdescent : baseEnd_3680837 < baseStart_3680837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680900 : List Nat := [2, 3, 2, 1, 3, 3, 1, 8]
def baseStart_3680900 : Nat := 118140960795 + 3680900 * 2 ^ 59
def prefixEnd_3680900 : Nat := 4983230072969 + 3 ^ 40 * 3680900 * 2
def baseEnd_3680900 : Nat := 70002627449435322056365

theorem tailTrace_3680900 : CollatzResearch.WordTrace tailWord_3680900 prefixEnd_3680900 70002627449435322056365 := by
  unfold tailWord_3680900
  simp only [CollatzResearch.WordTrace]
  refine ⟨67126726182367711257956077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89502301576490281677274769 67126726182367711257956077)
  ·
    refine ⟨25172522318387891721733529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67126726182367711257956077 25172522318387891721733529)
    ·
      refine ⟨18879391738790918791300147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25172522318387891721733529 18879391738790918791300147)
      ·
        refine ⟨28319087608186378186950221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18879391738790918791300147 28319087608186378186950221)
        ·
          refine ⟨10619657853069891820106333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28319087608186378186950221 10619657853069891820106333)
          ·
            refine ⟨3982371694901209432539875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10619657853069891820106333 3982371694901209432539875)
            ·
              refine ⟨5973557542351814148809813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3982371694901209432539875 5973557542351814148809813)
              ·
                refine ⟨70002627449435322056365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5973557542351814148809813 70002627449435322056365)
                ·
                  rfl

theorem cell23_3680900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 8].length) (baseStart_3680900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680900 prefixEnd_3680900 := by exact prefixLift 3680900
  have htrace : WordTrace (prefixWord ++ tailWord_3680900) baseStart_3680900 baseEnd_3680900 := by
    simpa [prefixWord, tailWord_3680900, baseEnd_3680900] using wordTrace_append hprefix tailTrace_3680900
  have hstable : (prefixWord ++ tailWord_3680900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680900).length < 2 ^ (prefixWord ++ tailWord_3680900).sum := by decide
  have hdescent : baseEnd_3680900 < baseStart_3680900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680938 : List Nat := [3, 1, 5, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3680938 : Nat := 118140960795 + 3680938 * 2 ^ 59
def prefixEnd_3680938 : Nat := 4983230072969 + 3 ^ 40 * 3680938 * 2
def baseEnd_3680938 : Nat := 630030151133208182282227

theorem tailTrace_3680938 : CollatzResearch.WordTrace tailWord_3680938 prefixEnd_3680938 630030151133208182282227 := by
  unfold tailWord_3680938
  simp only [CollatzResearch.WordTrace]
  refine ⟨33563709584649438751448867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89503225559065170003863645 33563709584649438751448867)
  ·
    refine ⟨50345564376974158127173301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33563709584649438751448867 50345564376974158127173301)
    ·
      refine ⟨4719896660341327324422497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50345564376974158127173301 4719896660341327324422497)
      ·
        refine ⟨3539922495255995493316873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4719896660341327324422497 3539922495255995493316873)
        ·
          refine ⟨2654941871441996619987655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3539922495255995493316873 2654941871441996619987655)
          ·
            refine ⟨3982412807162994929981483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654941871441996619987655 3982412807162994929981483)
            ·
              refine ⟨5973619210744492394972225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3982412807162994929981483 5973619210744492394972225)
              ·
                refine ⟨4480214408058369296229169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5973619210744492394972225 4480214408058369296229169)
                ·
                  refine ⟨3360160806043776972171877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4480214408058369296229169 3360160806043776972171877)
                  ·
                    refine ⟨630030151133208182282227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3360160806043776972171877 630030151133208182282227)
                    ·
                      rfl

theorem cell23_3680938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3680938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680938 prefixEnd_3680938 := by exact prefixLift 3680938
  have htrace : WordTrace (prefixWord ++ tailWord_3680938) baseStart_3680938 baseEnd_3680938 := by
    simpa [prefixWord, tailWord_3680938, baseEnd_3680938] using wordTrace_append hprefix tailTrace_3680938
  have hstable : (prefixWord ++ tailWord_3680938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680938).length < 2 ^ (prefixWord ++ tailWord_3680938).sum := by decide
  have hdescent : baseEnd_3680938 < baseStart_3680938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680943 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 2, 6]
def baseStart_3680943 : Nat := 118140960795 + 3680943 * 2 ^ 59
def prefixEnd_3680943 : Nat := 4983230072969 + 3 ^ 40 * 3680943 * 2
def baseEnd_3680943 : Nat := 630031006934299009094719

theorem tailTrace_3680943 : CollatzResearch.WordTrace tailWord_3680943 prefixEnd_3680943 630031006934299009094719 := by
  unfold tailWord_3680943
  simp only [CollatzResearch.WordTrace]
  refine ⟨134255020703579640859727483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89503347135719760573151655 134255020703579640859727483)
  ·
    refine ⟨201382531055369461289591225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134255020703579640859727483 201382531055369461289591225)
    ·
      refine ⟨151036898291527095967193419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201382531055369461289591225 151036898291527095967193419)
      ·
        refine ⟨226555347437290643950790129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151036898291527095967193419 226555347437290643950790129)
        ·
          refine ⟨169916510577967982963092597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226555347437290643950790129 169916510577967982963092597)
          ·
            refine ⟨15929672866684498402789931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169916510577967982963092597 15929672866684498402789931)
            ·
              refine ⟨23894509300026747604184897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15929672866684498402789931 23894509300026747604184897)
              ·
                refine ⟨17920881975020060703138673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23894509300026747604184897 17920881975020060703138673)
                ·
                  refine ⟨13440661481265045527354005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17920881975020060703138673 13440661481265045527354005)
                  ·
                    refine ⟨630031006934299009094719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13440661481265045527354005 630031006934299009094719)
                    ·
                      rfl

theorem cell23_3680943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 6].length) (baseStart_3680943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680943 prefixEnd_3680943 := by exact prefixLift 3680943
  have htrace : WordTrace (prefixWord ++ tailWord_3680943) baseStart_3680943 baseEnd_3680943 := by
    simpa [prefixWord, tailWord_3680943, baseEnd_3680943] using wordTrace_append hprefix tailTrace_3680943
  have hstable : (prefixWord ++ tailWord_3680943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680943).length < 2 ^ (prefixWord ++ tailWord_3680943).sum := by decide
  have hdescent : baseEnd_3680943 < baseStart_3680943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680953 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 4, 1, 5]
def baseStart_3680953 : Nat := 118140960795 + 3680953 * 2 ^ 59
def prefixEnd_3680953 : Nat := 4983230072969 + 3 ^ 40 * 3680953 * 2
def baseEnd_3680953 : Nat := 1890098155609441988159111

theorem tailTrace_3680953 : CollatzResearch.WordTrace tailWord_3680953 prefixEnd_3680953 1890098155609441988159111 := by
  unfold tailWord_3680953
  simp only [CollatzResearch.WordTrace]
  refine ⟨134255385433543412567591513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89503590289028941711727675 134255385433543412567591513)
  ·
    refine ⟨100691539075157559425693635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134255385433543412567591513 100691539075157559425693635)
    ·
      refine ⟨151037308612736339138540453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100691539075157559425693635 151037308612736339138540453)
      ·
        refine ⟨28319495364888063588476335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151037308612736339138540453 28319495364888063588476335)
        ·
          refine ⟨42479243047332095382714503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28319495364888063588476335 42479243047332095382714503)
          ·
            refine ⟨63718864570998143074071755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42479243047332095382714503 63718864570998143074071755)
            ·
              refine ⟨95578296856497214611107633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63718864570998143074071755 95578296856497214611107633)
              ·
                refine ⟨71683722642372910958330725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95578296856497214611107633 71683722642372910958330725)
                ·
                  refine ⟨13440697995444920804687011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71683722642372910958330725 13440697995444920804687011)
                  ·
                    refine ⟨20161046993167381207030517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13440697995444920804687011 20161046993167381207030517)
                    ·
                      refine ⟨1890098155609441988159111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20161046993167381207030517 1890098155609441988159111)
                      ·
                        rfl

theorem cell23_3680953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_3680953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680953 prefixEnd_3680953 := by exact prefixLift 3680953
  have htrace : WordTrace (prefixWord ++ tailWord_3680953) baseStart_3680953 baseEnd_3680953 := by
    simpa [prefixWord, tailWord_3680953, baseEnd_3680953] using wordTrace_append hprefix tailTrace_3680953
  have hstable : (prefixWord ++ tailWord_3680953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680953).length < 2 ^ (prefixWord ++ tailWord_3680953).sum := by decide
  have hdescent : baseEnd_3680953 < baseStart_3680953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3680961 : List Nat := [1, 2, 6, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3680961 : Nat := 118140960795 + 3680961 * 2 ^ 59
def prefixEnd_3680961 : Nat := 4983230072969 + 3 ^ 40 * 3680961 * 2
def baseEnd_3680961 : Nat := 1890102263454677956859075

theorem tailTrace_3680961 : CollatzResearch.WordTrace tailWord_3680961 prefixEnd_3680961 1890102263454677956859075 := by
  unfold tailWord_3680961
  simp only [CollatzResearch.WordTrace]
  refine ⟨134255677217514429933882737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89503784811676286622588491 134255677217514429933882737)
  ·
    refine ⟨100691757913135822450412053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134255677217514429933882737 100691757913135822450412053)
    ·
      refine ⟨4719926152178241677363065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100691757913135822450412053 4719926152178241677363065)
      ·
        refine ⟨3539944614133681258022299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4719926152178241677363065 3539944614133681258022299)
        ·
          refine ⟨5309916921200521887033449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3539944614133681258022299 5309916921200521887033449)
          ·
            refine ⟨3982437690900391415275087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5309916921200521887033449 3982437690900391415275087)
            ·
              refine ⟨5973656536350587122912631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3982437690900391415275087 5973656536350587122912631)
              ·
                refine ⟨8960484804525880684368947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5973656536350587122912631 8960484804525880684368947)
                ·
                  refine ⟨13440727206788821026553421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8960484804525880684368947 13440727206788821026553421)
                  ·
                    refine ⟨5040272702545807884957533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13440727206788821026553421 5040272702545807884957533)
                    ·
                      refine ⟨1890102263454677956859075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5040272702545807884957533 1890102263454677956859075)
                      ·
                        rfl

theorem cell23_3680961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3680961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3680961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3680961 prefixEnd_3680961 := by exact prefixLift 3680961
  have htrace : WordTrace (prefixWord ++ tailWord_3680961) baseStart_3680961 baseEnd_3680961 := by
    simpa [prefixWord, tailWord_3680961, baseEnd_3680961] using wordTrace_append hprefix tailTrace_3680961
  have hstable : (prefixWord ++ tailWord_3680961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3680961).length < 2 ^ (prefixWord ++ tailWord_3680961).sum := by decide
  have hdescent : baseEnd_3680961 < baseStart_3680961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3680961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681012 : List Nat := [2, 6, 1, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_3681012 : Nat := 118140960795 + 3681012 * 2 ^ 59
def prefixEnd_3681012 : Nat := 4983230072969 + 3 ^ 40 * 3681012 * 2
def baseEnd_3681012 : Nat := 1890128450968057257321341

theorem tailTrace_3681012 : CollatzResearch.WordTrace tailWord_3681012 prefixEnd_3681012 1890128450968057257321341 := by
  unfold tailWord_3681012
  simp only [CollatzResearch.WordTrace]
  refine ⟨67128768670164832821994645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89505024893553110429326193 67128768670164832821994645)
  ·
    refine ⟨3146661031413976538530999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67128768670164832821994645 3146661031413976538530999)
    ·
      refine ⟨4719991547120964807796499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3146661031413976538530999 4719991547120964807796499)
      ·
        refine ⟨7079987320681447211694749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4719991547120964807796499 7079987320681447211694749)
        ·
          refine ⟨2654995245255542704385531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7079987320681447211694749 2654995245255542704385531)
          ·
            refine ⟨3982492867883314056578297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654995245255542704385531 3982492867883314056578297)
            ·
              refine ⟨2986869650912485542433723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3982492867883314056578297 2986869650912485542433723)
              ·
                refine ⟨4480304476368728313650585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2986869650912485542433723 4480304476368728313650585)
                ·
                  refine ⟨3360228357276546235237939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4480304476368728313650585 3360228357276546235237939)
                  ·
                    refine ⟨5040342535914819352856909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3360228357276546235237939 5040342535914819352856909)
                    ·
                      refine ⟨1890128450968057257321341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5040342535914819352856909 1890128450968057257321341)
                      ·
                        rfl

theorem cell23_3681012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_3681012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681012 prefixEnd_3681012 := by exact prefixLift 3681012
  have htrace : WordTrace (prefixWord ++ tailWord_3681012) baseStart_3681012 baseEnd_3681012 := by
    simpa [prefixWord, tailWord_3681012, baseEnd_3681012] using wordTrace_append hprefix tailTrace_3681012
  have hstable : (prefixWord ++ tailWord_3681012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681012).length < 2 ^ (prefixWord ++ tailWord_3681012).sum := by decide
  have hdescent : baseEnd_3681012 < baseStart_3681012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681033 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 2, 8]
def baseStart_3681033 : Nat := 118140960795 + 3681033 * 2 ^ 59
def prefixEnd_3681033 : Nat := 4983230072969 + 3 ^ 40 * 3681033 * 2
def baseEnd_3681033 : Nat := 630046411353933891719581

theorem tailTrace_3681033 : CollatzResearch.WordTrace tailWord_3681033 prefixEnd_3681033 630046411353933891719581 := by
  unfold tailWord_3681033
  simp only [CollatzResearch.WordTrace]
  refine ⟨134258303273253586230503753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89505535515502390820335835 134258303273253586230503753)
  ·
    refine ⟨100693727454940189672877815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134258303273253586230503753 100693727454940189672877815)
    ·
      refine ⟨151040591182410284509316723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100693727454940189672877815 151040591182410284509316723)
      ·
        refine ⟨226560886773615426763975085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151040591182410284509316723 226560886773615426763975085)
        ·
          refine ⟨84960332540105785036490657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226560886773615426763975085 84960332540105785036490657)
          ·
            refine ⟨63720249405079338777367993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84960332540105785036490657 63720249405079338777367993)
            ·
              refine ⟨47790187053809504083025995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63720249405079338777367993 47790187053809504083025995)
              ·
                refine ⟨71685280580714256124538993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47790187053809504083025995 71685280580714256124538993)
                ·
                  refine ⟨53763960435535692093404245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71685280580714256124538993 53763960435535692093404245)
                  ·
                    refine ⟨630046411353933891719581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53763960435535692093404245 630046411353933891719581)
                    ·
                      rfl

theorem cell23_3681033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 8].length) (baseStart_3681033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681033 prefixEnd_3681033 := by exact prefixLift 3681033
  have htrace : WordTrace (prefixWord ++ tailWord_3681033) baseStart_3681033 baseEnd_3681033 := by
    simpa [prefixWord, tailWord_3681033, baseEnd_3681033] using wordTrace_append hprefix tailTrace_3681033
  have hstable : (prefixWord ++ tailWord_3681033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681033).length < 2 ^ (prefixWord ++ tailWord_3681033).sum := by decide
  have hdescent : baseEnd_3681033 < baseStart_3681033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681057 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 2, 4, 2]
def baseStart_3681057 : Nat := 118140960795 + 3681057 * 2 ^ 59
def prefixEnd_3681057 : Nat := 4983230072969 + 3 ^ 40 * 3681057 * 2
def baseEnd_3681057 : Nat := 1890151557597509581258633

theorem tailTrace_3681057 : CollatzResearch.WordTrace tailWord_3681057 prefixEnd_3681057 1890151557597509581258633 := by
  unfold tailWord_3681057
  simp only [CollatzResearch.WordTrace]
  refine ⟨134259178625166638329377425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89506119083444425552918283 134259178625166638329377425)
  ·
    refine ⟨100694383968874978747033069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134259178625166638329377425 100694383968874978747033069)
    ·
      refine ⟨37760393988328117030137401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100694383968874978747033069 37760393988328117030137401)
      ·
        refine ⟨28320295491246087772603051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37760393988328117030137401 28320295491246087772603051)
        ·
          refine ⟨42480443236869131658904577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28320295491246087772603051 42480443236869131658904577)
          ·
            refine ⟨31860332427651848744178433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42480443236869131658904577 31860332427651848744178433)
            ·
              refine ⟨23895249320738886558133825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31860332427651848744178433 23895249320738886558133825)
              ·
                refine ⟨17921436990554164918600369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23895249320738886558133825 17921436990554164918600369)
                ·
                  refine ⟨13441077742915623688950277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17921436990554164918600369 13441077742915623688950277)
                  ·
                    refine ⟨2520202076796679441678177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13441077742915623688950277 2520202076796679441678177)
                    ·
                      refine ⟨1890151557597509581258633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2520202076796679441678177 1890151557597509581258633)
                      ·
                        rfl

theorem cell23_3681057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_3681057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681057 prefixEnd_3681057 := by exact prefixLift 3681057
  have htrace : WordTrace (prefixWord ++ tailWord_3681057) baseStart_3681057 baseEnd_3681057 := by
    simpa [prefixWord, tailWord_3681057, baseEnd_3681057] using wordTrace_append hprefix tailTrace_3681057
  have hstable : (prefixWord ++ tailWord_3681057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681057).length < 2 ^ (prefixWord ++ tailWord_3681057).sum := by decide
  have hdescent : baseEnd_3681057 < baseStart_3681057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681080 : List Nat := [2, 1, 2, 1, 3, 2, 1, 5, 6]
def baseStart_3681080 : Nat := 118140960795 + 3681080 * 2 ^ 59
def prefixEnd_3681080 : Nat := 4983230072969 + 3 ^ 40 * 3681080 * 2
def baseEnd_3681080 : Nat := 210018151961395887919003

theorem tailTrace_3681080 : CollatzResearch.WordTrace tailWord_3681080 prefixEnd_3681080 210018151961395887919003 := by
  unfold tailWord_3681080
  simp only [CollatzResearch.WordTrace]
  refine ⟨67130008752041656628732347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89506678336055542171643129 67130008752041656628732347)
  ·
    refine ⟨100695013128062484943098521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67130008752041656628732347 100695013128062484943098521)
    ·
      refine ⟨75521259846046863707323891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100695013128062484943098521 75521259846046863707323891)
      ·
        refine ⟨113281889769070295560985837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75521259846046863707323891 113281889769070295560985837)
        ·
          refine ⟨42480708663401360835369689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113281889769070295560985837 42480708663401360835369689)
          ·
            refine ⟨31860531497551020626527267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42480708663401360835369689 31860531497551020626527267)
            ·
              refine ⟨47790797246326530939790901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31860531497551020626527267 47790797246326530939790901)
              ·
                refine ⟨4480387241843112275605397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47790797246326530939790901 4480387241843112275605397)
                ·
                  refine ⟨210018151961395887919003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4480387241843112275605397 210018151961395887919003)
                  ·
                    rfl

theorem cell23_3681080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 5, 6].length) (baseStart_3681080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681080 prefixEnd_3681080 := by exact prefixLift 3681080
  have htrace : WordTrace (prefixWord ++ tailWord_3681080) baseStart_3681080 baseEnd_3681080 := by
    simpa [prefixWord, tailWord_3681080, baseEnd_3681080] using wordTrace_append hprefix tailTrace_3681080
  have hstable : (prefixWord ++ tailWord_3681080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681080).length < 2 ^ (prefixWord ++ tailWord_3681080).sum := by decide
  have hdescent : baseEnd_3681080 < baseStart_3681080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681124 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 3, 1, 3]
def baseStart_3681124 : Nat := 118140960795 + 3681124 * 2 ^ 59
def prefixEnd_3681124 : Nat := 4983230072969 + 3 ^ 40 * 3681124 * 2
def baseEnd_3681124 : Nat := 1890185960801360819120825

theorem tailTrace_3681124 : CollatzResearch.WordTrace tailWord_3681124 prefixEnd_3681124 1890185960801360819120825 := by
  unfold tailWord_3681124
  simp only [CollatzResearch.WordTrace]
  refine ⟨67130811157961954386033213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89507748210615939181377617 67130811157961954386033213)
  ·
    refine ⟨25174054184235732894762455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67130811157961954386033213 25174054184235732894762455)
    ·
      refine ⟨37761081276353599342143683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25174054184235732894762455 37761081276353599342143683)
      ·
        refine ⟨56641621914530399013215525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37761081276353599342143683 56641621914530399013215525)
        ·
          refine ⟨10620304108974449814977911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56641621914530399013215525 10620304108974449814977911)
          ·
            refine ⟨15930456163461674722466867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10620304108974449814977911 15930456163461674722466867)
            ·
              refine ⟨23895684245192512083700301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15930456163461674722466867 23895684245192512083700301)
              ·
                refine ⟨8960881591947192031387613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23895684245192512083700301 8960881591947192031387613)
                ·
                  refine ⟨3360330596980197011770355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8960881591947192031387613 3360330596980197011770355)
                  ·
                    refine ⟨5040495895470295517655533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3360330596980197011770355 5040495895470295517655533)
                    ·
                      refine ⟨1890185960801360819120825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5040495895470295517655533 1890185960801360819120825)
                      ·
                        rfl

theorem cell23_3681124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_3681124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681124 prefixEnd_3681124 := by exact prefixLift 3681124
  have htrace : WordTrace (prefixWord ++ tailWord_3681124) baseStart_3681124 baseEnd_3681124 := by
    simpa [prefixWord, tailWord_3681124, baseEnd_3681124] using wordTrace_append hprefix tailTrace_3681124
  have hstable : (prefixWord ++ tailWord_3681124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681124).length < 2 ^ (prefixWord ++ tailWord_3681124).sum := by decide
  have hdescent : baseEnd_3681124 < baseStart_3681124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681147 : List Nat := [1, 1, 1, 1, 1, 5, 3, 4, 1, 1, 4]
def baseStart_3681147 : Nat := 118140960795 + 3681147 * 2 ^ 59
def prefixEnd_3681147 : Nat := 4983230072969 + 3 ^ 40 * 3681147 * 2
def baseEnd_3681147 : Nat := 1890197770856414229133219

theorem tailTrace_3681147 : CollatzResearch.WordTrace tailWord_3681147 prefixEnd_3681147 1890197770856414229133219 := by
  unfold tailWord_3681147
  simp only [CollatzResearch.WordTrace]
  refine ⟨134262461194840583700153695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89508307463227055800102463 134262461194840583700153695)
  ·
    refine ⟨201393691792260875550230543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134262461194840583700153695 201393691792260875550230543)
    ·
      refine ⟨302090537688391313325345815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201393691792260875550230543 302090537688391313325345815)
      ·
        refine ⟨453135806532586969988018723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302090537688391313325345815 453135806532586969988018723)
        ·
          refine ⟨679703709798880454982028085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453135806532586969988018723 679703709798880454982028085)
          ·
            refine ⟨63722222793645042654565133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 679703709798880454982028085 63722222793645042654565133)
            ·
              refine ⟨23895833547616890995461925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63722222793645042654565133 23895833547616890995461925)
              ·
                refine ⟨4480468790178167061649111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23895833547616890995461925 4480468790178167061649111)
                ·
                  refine ⟨6720703185267250592473667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4480468790178167061649111 6720703185267250592473667)
                  ·
                    refine ⟨10081054777900875888710501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6720703185267250592473667 10081054777900875888710501)
                    ·
                      refine ⟨1890197770856414229133219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10081054777900875888710501 1890197770856414229133219)
                      ·
                        rfl

theorem cell23_3681147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 1, 4].length) (baseStart_3681147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681147 prefixEnd_3681147 := by exact prefixLift 3681147
  have htrace : WordTrace (prefixWord ++ tailWord_3681147) baseStart_3681147 baseEnd_3681147 := by
    simpa [prefixWord, tailWord_3681147, baseEnd_3681147] using wordTrace_append hprefix tailTrace_3681147
  have hstable : (prefixWord ++ tailWord_3681147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681147).length < 2 ^ (prefixWord ++ tailWord_3681147).sum := by decide
  have hdescent : baseEnd_3681147 < baseStart_3681147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681157 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 4, 4]
def baseStart_3681157 : Nat := 118140960795 + 3681157 * 2 ^ 59
def prefixEnd_3681157 : Nat := 4983230072969 + 3 ^ 40 * 3681157 * 2
def baseEnd_3681157 : Nat := 630067635220986396669391

theorem tailTrace_3681157 : CollatzResearch.WordTrace tailWord_3681157 prefixEnd_3681157 630067635220986396669391 := by
  unfold tailWord_3681157
  simp only [CollatzResearch.WordTrace]
  refine ⟨134262825924804355408017725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89508550616536236938678483 134262825924804355408017725)
  ·
    refine ⟨50348559721801633278006647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134262825924804355408017725 50348559721801633278006647)
    ·
      refine ⟨75522839582702449917009971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50348559721801633278006647 75522839582702449917009971)
      ·
        refine ⟨113284259374053674875514957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75522839582702449917009971 113284259374053674875514957)
        ·
          refine ⟨42481597265270128078318109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113284259374053674875514957 42481597265270128078318109)
          ·
            refine ⟨15930598974476298029369291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42481597265270128078318109 15930598974476298029369291)
            ·
              refine ⟨23895898461714447044053937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15930598974476298029369291 23895898461714447044053937)
              ·
                refine ⟨17921923846285835283040453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23895898461714447044053937 17921923846285835283040453)
                ·
                  refine ⟨3360360721178594115570085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17921923846285835283040453 3360360721178594115570085)
                  ·
                    refine ⟨630067635220986396669391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3360360721178594115570085 630067635220986396669391)
                    ·
                      rfl

theorem cell23_3681157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_3681157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681157 prefixEnd_3681157 := by exact prefixLift 3681157
  have htrace : WordTrace (prefixWord ++ tailWord_3681157) baseStart_3681157 baseEnd_3681157 := by
    simpa [prefixWord, tailWord_3681157, baseEnd_3681157] using wordTrace_append hprefix tailTrace_3681157
  have hstable : (prefixWord ++ tailWord_3681157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681157).length < 2 ^ (prefixWord ++ tailWord_3681157).sum := by decide
  have hdescent : baseEnd_3681157 < baseStart_3681157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681164 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 5, 2, 2]
def baseStart_3681164 : Nat := 118140960795 + 3681164 * 2 ^ 59
def prefixEnd_3681164 : Nat := 4983230072969 + 3 ^ 40 * 3681164 * 2
def baseEnd_3681164 : Nat := 1890206500027540662620641

theorem tailTrace_3681164 : CollatzResearch.WordTrace tailWord_3681164 prefixEnd_3681164 1890206500027540662620641 := by
  unfold tailWord_3681164
  simp only [CollatzResearch.WordTrace]
  refine ⟨67131540617889497801761273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89508720823852663735681697 67131540617889497801761273)
  ·
    refine ⟨50348655463417123351320955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67131540617889497801761273 50348655463417123351320955)
    ·
      refine ⟨75522983195125685026981433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50348655463417123351320955 75522983195125685026981433)
      ·
        refine ⟨56642237396344263770236075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75522983195125685026981433 56642237396344263770236075)
        ·
          refine ⟨84963356094516395655354113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56642237396344263770236075 84963356094516395655354113)
          ·
            refine ⟨63722517070887296741515585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84963356094516395655354113 63722517070887296741515585)
            ·
              refine ⟨47791887803165472556136689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63722517070887296741515585 47791887803165472556136689)
              ·
                refine ⟨35843915852374104417102517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47791887803165472556136689 35843915852374104417102517)
                ·
                  refine ⟨3360367111160072289103361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35843915852374104417102517 3360367111160072289103361)
                  ·
                    refine ⟨2520275333370054216827521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3360367111160072289103361 2520275333370054216827521)
                    ·
                      refine ⟨1890206500027540662620641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2520275333370054216827521 1890206500027540662620641)
                      ·
                        rfl

theorem cell23_3681164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_3681164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681164 prefixEnd_3681164 := by exact prefixLift 3681164
  have htrace : WordTrace (prefixWord ++ tailWord_3681164) baseStart_3681164 baseEnd_3681164 := by
    simpa [prefixWord, tailWord_3681164, baseEnd_3681164] using wordTrace_append hprefix tailTrace_3681164
  have hstable : (prefixWord ++ tailWord_3681164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681164).length < 2 ^ (prefixWord ++ tailWord_3681164).sum := by decide
  have hdescent : baseEnd_3681164 < baseStart_3681164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681191 : List Nat := [1, 1, 6, 1, 3, 1, 1, 3, 2, 4]
def baseStart_3681191 : Nat := 118140960795 + 3681191 * 2 ^ 59
def prefixEnd_3681191 : Nat := 4983230072969 + 3 ^ 40 * 3681191 * 2
def baseEnd_3681191 : Nat := 630073454668404018994339

theorem tailTrace_3681191 : CollatzResearch.WordTrace tailWord_3681191 prefixEnd_3681191 630073454668404018994339 := by
  unfold tailWord_3681191
  simp only [CollatzResearch.WordTrace]
  refine ⟨134264066006681179214755427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89509377337787452809836951 134264066006681179214755427)
  ·
    refine ⟨201396099010021768822133141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134264066006681179214755427 201396099010021768822133141)
    ·
      refine ⟨9440442141094770413537491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 201396099010021768822133141 9440442141094770413537491)
      ·
        refine ⟨14160663211642155620306237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9440442141094770413537491 14160663211642155620306237)
        ·
          refine ⟨5310248704365808357614839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14160663211642155620306237 5310248704365808357614839)
          ·
            refine ⟨7965373056548712536422259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5310248704365808357614839 7965373056548712536422259)
            ·
              refine ⟨11948059584823068804633389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7965373056548712536422259 11948059584823068804633389)
              ·
                refine ⟨4480522344308650801737521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11948059584823068804633389 4480522344308650801737521)
                ·
                  refine ⟨3360391758231488101303141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4480522344308650801737521 3360391758231488101303141)
                  ·
                    refine ⟨630073454668404018994339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3360391758231488101303141 630073454668404018994339)
                    ·
                      rfl

theorem cell23_3681191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_3681191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681191 prefixEnd_3681191 := by exact prefixLift 3681191
  have htrace : WordTrace (prefixWord ++ tailWord_3681191) baseStart_3681191 baseEnd_3681191 := by
    simpa [prefixWord, tailWord_3681191, baseEnd_3681191] using wordTrace_append hprefix tailTrace_3681191
  have hstable : (prefixWord ++ tailWord_3681191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681191).length < 2 ^ (prefixWord ++ tailWord_3681191).sum := by decide
  have hdescent : baseEnd_3681191 < baseStart_3681191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681204 : List Nat := [2, 5, 2, 1, 1, 1, 2, 9]
def baseStart_3681204 : Nat := 118140960795 + 3681204 * 2 ^ 59
def prefixEnd_3681204 : Nat := 4983230072969 + 3 ^ 40 * 3681204 * 2
def baseEnd_3681204 : Nat := 70008408861248907634091

theorem tailTrace_3681204 : CollatzResearch.WordTrace tailWord_3681204 prefixEnd_3681204 70008408861248907634091 := by
  unfold tailWord_3681204
  simp only [CollatzResearch.WordTrace]
  refine ⟨67132270077817041217489333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89509693437089388289985777 67132270077817041217489333)
  ·
    refine ⟨6293650319795347614139625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67132270077817041217489333 6293650319795347614139625)
    ·
      refine ⟨4720237739846510710604719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6293650319795347614139625 4720237739846510710604719)
      ·
        refine ⟨7080356609769766065907079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4720237739846510710604719 7080356609769766065907079)
        ·
          refine ⟨10620534914654649098860619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7080356609769766065907079 10620534914654649098860619)
          ·
            refine ⟨15930802371981973648290929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10620534914654649098860619 15930802371981973648290929)
            ·
              refine ⟨11948101778986480236218197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15930802371981973648290929 11948101778986480236218197)
              ·
                refine ⟨70008408861248907634091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11948101778986480236218197 70008408861248907634091)
                ·
                  rfl

theorem cell23_3681204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 9].length) (baseStart_3681204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681204 prefixEnd_3681204 := by exact prefixLift 3681204
  have htrace : WordTrace (prefixWord ++ tailWord_3681204) baseStart_3681204 baseEnd_3681204 := by
    simpa [prefixWord, tailWord_3681204, baseEnd_3681204] using wordTrace_append hprefix tailTrace_3681204
  have hstable : (prefixWord ++ tailWord_3681204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681204).length < 2 ^ (prefixWord ++ tailWord_3681204).sum := by decide
  have hdescent : baseEnd_3681204 < baseStart_3681204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681214 : List Nat := [4, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3]
def baseStart_3681214 : Nat := 118140960795 + 3681214 * 2 ^ 59
def prefixEnd_3681214 : Nat := 4983230072969 + 3 ^ 40 * 3681214 * 2
def baseEnd_3681214 : Nat := 1890232174060265466995411

theorem tailTrace_3681214 : CollatzResearch.WordTrace tailWord_3681214 prefixEnd_3681214 1890232174060265466995411 := by
  unfold tailWord_3681214
  simp only [CollatzResearch.WordTrace]
  refine ⟨16783113110699731767855337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89509936590398569428561797 16783113110699731767855337)
  ·
    refine ⟨12587334833024798825891503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16783113110699731767855337 12587334833024798825891503)
    ·
      refine ⟨18881002249537198238837255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12587334833024798825891503 18881002249537198238837255)
      ·
        refine ⟨28321503374305797358255883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18881002249537198238837255 28321503374305797358255883)
        ·
          refine ⟨42482255061458696037383825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28321503374305797358255883 42482255061458696037383825)
          ·
            refine ⟨31861691296094022028037869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42482255061458696037383825 31861691296094022028037869)
            ·
              refine ⟨11948134236035258260514201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31861691296094022028037869 11948134236035258260514201)
              ·
                refine ⟨8961100677026443695385651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11948134236035258260514201 8961100677026443695385651)
                ·
                  refine ⟨13441651015539665543078477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8961100677026443695385651 13441651015539665543078477)
                  ·
                    refine ⟨5040619130827374578654429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13441651015539665543078477 5040619130827374578654429)
                    ·
                      refine ⟨1890232174060265466995411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5040619130827374578654429 1890232174060265466995411)
                      ·
                        rfl

theorem cell23_3681214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_3681214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681214 prefixEnd_3681214 := by exact prefixLift 3681214
  have htrace : WordTrace (prefixWord ++ tailWord_3681214) baseStart_3681214 baseEnd_3681214 := by
    simpa [prefixWord, tailWord_3681214, baseEnd_3681214] using wordTrace_append hprefix tailTrace_3681214
  have hstable : (prefixWord ++ tailWord_3681214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681214).length < 2 ^ (prefixWord ++ tailWord_3681214).sum := by decide
  have hdescent : baseEnd_3681214 < baseStart_3681214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681231 : List Nat := [1, 1, 2, 1, 1, 7, 2, 2, 2, 1, 3]
def baseStart_3681231 : Nat := 118140960795 + 3681231 * 2 ^ 59
def prefixEnd_3681231 : Nat := 4983230072969 + 3 ^ 40 * 3681231 * 2
def baseEnd_3681231 : Nat := 1890240903231391900482833

theorem tailTrace_3681231 : CollatzResearch.WordTrace tailWord_3681231 prefixEnd_3681231 1890240903231391900482833 := by
  unfold tailWord_3681231
  simp only [CollatzResearch.WordTrace]
  refine ⟨134265524926536266046211547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89510349951024177364141031 134265524926536266046211547)
  ·
    refine ⟨201398287389804399069317321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134265524926536266046211547 201398287389804399069317321)
    ·
      refine ⟨151048715542353299301987991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201398287389804399069317321 151048715542353299301987991)
      ·
        refine ⟨226573073313529948952981987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151048715542353299301987991 226573073313529948952981987)
        ·
          refine ⟨339859609970294923429472981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226573073313529948952981987 339859609970294923429472981)
          ·
            refine ⟨7965459608678787267878273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 339859609970294923429472981 7965459608678787267878273)
            ·
              refine ⟨5974094706509090450908705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7965459608678787267878273 5974094706509090450908705)
              ·
                refine ⟨4480571029881817838181529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5974094706509090450908705 4480571029881817838181529)
                ·
                  refine ⟨3360428272411363378636147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4480571029881817838181529 3360428272411363378636147)
                  ·
                    refine ⟨5040642408617045067954221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3360428272411363378636147 5040642408617045067954221)
                    ·
                      refine ⟨1890240903231391900482833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5040642408617045067954221 1890240903231391900482833)
                      ·
                        rfl

theorem cell23_3681231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 2, 1, 3].length) (baseStart_3681231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681231 prefixEnd_3681231 := by exact prefixLift 3681231
  have htrace : WordTrace (prefixWord ++ tailWord_3681231) baseStart_3681231 baseEnd_3681231 := by
    simpa [prefixWord, tailWord_3681231, baseEnd_3681231] using wordTrace_append hprefix tailTrace_3681231
  have hstable : (prefixWord ++ tailWord_3681231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681231).length < 2 ^ (prefixWord ++ tailWord_3681231).sum := by decide
  have hdescent : baseEnd_3681231 < baseStart_3681231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681282 : List Nat := [3, 4, 1, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3681282 : Nat := 118140960795 + 3681282 * 2 ^ 59
def prefixEnd_3681282 : Nat := 4983230072969 + 3 ^ 40 * 3681282 * 2
def baseEnd_3681282 : Nat := 1890267090744771200945099

theorem tailTrace_3681282 : CollatzResearch.WordTrace tailWord_3681282 prefixEnd_3681282 1890267090744771200945099 := by
  unfold tailWord_3681282
  simp only [CollatzResearch.WordTrace]
  refine ⟨33566846262337875439079525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89511590032901001170878733 33566846262337875439079525)
  ·
    refine ⟨6293783674188351644827411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33566846262337875439079525 6293783674188351644827411)
    ·
      refine ⟨9440675511282527467241117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6293783674188351644827411 9440675511282527467241117)
      ·
        refine ⟨3540253316730947800215419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9440675511282527467241117 3540253316730947800215419)
        ·
          refine ⟨5310379975096421700323129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3540253316730947800215419 5310379975096421700323129)
          ·
            refine ⟨3982784981322316275242347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5310379975096421700323129 3982784981322316275242347)
            ·
              refine ⟨5974177471983474412863521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3982784981322316275242347 5974177471983474412863521)
              ·
                refine ⟨4480633103987605809647641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5974177471983474412863521 4480633103987605809647641)
                ·
                  refine ⟨3360474827990704357235731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4480633103987605809647641 3360474827990704357235731)
                  ·
                    refine ⟨5040712241986056535853597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3360474827990704357235731 5040712241986056535853597)
                    ·
                      refine ⟨1890267090744771200945099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5040712241986056535853597 1890267090744771200945099)
                      ·
                        rfl

theorem cell23_3681282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3681282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681282 prefixEnd_3681282 := by exact prefixLift 3681282
  have htrace : WordTrace (prefixWord ++ tailWord_3681282) baseStart_3681282 baseEnd_3681282 := by
    simpa [prefixWord, tailWord_3681282, baseEnd_3681282] using wordTrace_append hprefix tailTrace_3681282
  have hstable : (prefixWord ++ tailWord_3681282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681282).length < 2 ^ (prefixWord ++ tailWord_3681282).sum := by decide
  have hdescent : baseEnd_3681282 < baseStart_3681282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681288 : List Nat := [2, 1, 3, 2, 1, 3, 3, 2, 2, 2, 2]
def baseStart_3681288 : Nat := 118140960795 + 3681288 * 2 ^ 59
def prefixEnd_3681288 : Nat := 4983230072969 + 3 ^ 40 * 3681288 * 2
def baseEnd_3681288 : Nat := 1890270171628698177470071

theorem tailTrace_3681288 : CollatzResearch.WordTrace tailWord_3681288 prefixEnd_3681288 1890270171628698177470071 := by
  unfold tailWord_3681288
  simp only [CollatzResearch.WordTrace]
  refine ⟨67133801943664882390518259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89511735924886509854024345 67133801943664882390518259)
  ·
    refine ⟨100700702915497323585777389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67133801943664882390518259 100700702915497323585777389)
    ·
      refine ⟨37762763593311496344666521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100700702915497323585777389 37762763593311496344666521)
      ·
        refine ⟨28322072694983622258499891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37762763593311496344666521 28322072694983622258499891)
        ·
          refine ⟨42483109042475433387749837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28322072694983622258499891 42483109042475433387749837)
          ·
            refine ⟨15931165890928287520406189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42483109042475433387749837 15931165890928287520406189)
            ·
              refine ⟨5974187209098107820152321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15931165890928287520406189 5974187209098107820152321)
              ·
                refine ⟨4480640406823580865114241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5974187209098107820152321 4480640406823580865114241)
                ·
                  refine ⟨3360480305117685648835681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4480640406823580865114241 3360480305117685648835681)
                  ·
                    refine ⟨2520360228838264236626761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3360480305117685648835681 2520360228838264236626761)
                    ·
                      refine ⟨1890270171628698177470071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2520360228838264236626761 1890270171628698177470071)
                      ·
                        rfl

theorem cell23_3681288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_3681288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681288 prefixEnd_3681288 := by exact prefixLift 3681288
  have htrace : WordTrace (prefixWord ++ tailWord_3681288) baseStart_3681288 baseEnd_3681288 := by
    simpa [prefixWord, tailWord_3681288, baseEnd_3681288] using wordTrace_append hprefix tailTrace_3681288
  have hstable : (prefixWord ++ tailWord_3681288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681288).length < 2 ^ (prefixWord ++ tailWord_3681288).sum := by decide
  have hdescent : baseEnd_3681288 < baseStart_3681288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681294 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 7]
def baseStart_3681294 : Nat := 118140960795 + 3681294 * 2 ^ 59
def prefixEnd_3681294 : Nat := 4983230072969 + 3 ^ 40 * 3681294 * 2
def baseEnd_3681294 : Nat := 210030361390291683777227

theorem tailTrace_3681294 : CollatzResearch.WordTrace tailWord_3681294 prefixEnd_3681294 210030361390291683777227 := by
  unfold tailWord_3681294
  simp only [CollatzResearch.WordTrace]
  refine ⟨16783477840663503475719367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89511881816872018537169957 16783477840663503475719367)
  ·
    refine ⟨25175216760995255213579051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16783477840663503475719367 25175216760995255213579051)
    ·
      refine ⟨37762825141492882820368577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25175216760995255213579051 37762825141492882820368577)
      ·
        refine ⟨28322118856119662115276433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37762825141492882820368577 28322118856119662115276433)
        ·
          refine ⟨21241589142089746586457325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28322118856119662115276433 21241589142089746586457325)
          ·
            refine ⟨7965595928283654969921497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21241589142089746586457325 7965595928283654969921497)
            ·
              refine ⟨5974196946212741227441123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7965595928283654969921497 5974196946212741227441123)
              ·
                refine ⟨8961295419319111841161685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5974196946212741227441123 8961295419319111841161685)
                ·
                  refine ⟨210030361390291683777227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8961295419319111841161685 210030361390291683777227)
                  ·
                    rfl

theorem cell23_3681294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_3681294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681294 prefixEnd_3681294 := by exact prefixLift 3681294
  have htrace : WordTrace (prefixWord ++ tailWord_3681294) baseStart_3681294 baseEnd_3681294 := by
    simpa [prefixWord, tailWord_3681294, baseEnd_3681294] using wordTrace_append hprefix tailTrace_3681294
  have hstable : (prefixWord ++ tailWord_3681294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681294).length < 2 ^ (prefixWord ++ tailWord_3681294).sum := by decide
  have hdescent : baseEnd_3681294 < baseStart_3681294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681304 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 2, 3, 3]
def baseStart_3681304 : Nat := 118140960795 + 3681304 * 2 ^ 59
def prefixEnd_3681304 : Nat := 4983230072969 + 3 ^ 40 * 3681304 * 2
def baseEnd_3681304 : Nat := 1890278387319170114869997

theorem tailTrace_3681304 : CollatzResearch.WordTrace tailWord_3681304 prefixEnd_3681304 1890278387319170114869997 := by
  unfold tailWord_3681304
  simp only [CollatzResearch.WordTrace]
  refine ⟨67134093727635899756809483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89512124970181199675745977 67134093727635899756809483)
  ·
    refine ⟨100701140591453849635214225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67134093727635899756809483 100701140591453849635214225)
    ·
      refine ⟨75525855443590387226410669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100701140591453849635214225 75525855443590387226410669)
      ·
        refine ⟨28322195791346395209904001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75525855443590387226410669 28322195791346395209904001)
        ·
          refine ⟨21241646843509796407428001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28322195791346395209904001 21241646843509796407428001)
          ·
            refine ⟨15931235132632347305571001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21241646843509796407428001 15931235132632347305571001)
            ·
              refine ⟨11948426349474260479178251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15931235132632347305571001 11948426349474260479178251)
              ·
                refine ⟨17922639524211390718767377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11948426349474260479178251 17922639524211390718767377)
                ·
                  refine ⟨13441979643158543039075533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17922639524211390718767377 13441979643158543039075533)
                  ·
                    refine ⟨5040742366184453639653325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13441979643158543039075533 5040742366184453639653325)
                    ·
                      refine ⟨1890278387319170114869997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5040742366184453639653325 1890278387319170114869997)
                      ·
                        rfl

theorem cell23_3681304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_3681304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681304 prefixEnd_3681304 := by exact prefixLift 3681304
  have htrace : WordTrace (prefixWord ++ tailWord_3681304) baseStart_3681304 baseEnd_3681304 := by
    simpa [prefixWord, tailWord_3681304, baseEnd_3681304] using wordTrace_append hprefix tailTrace_3681304
  have hstable : (prefixWord ++ tailWord_3681304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681304).length < 2 ^ (prefixWord ++ tailWord_3681304).sum := by decide
  have hdescent : baseEnd_3681304 < baseStart_3681304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681344 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 4]
def baseStart_3681344 : Nat := 118140960795 + 3681344 * 2 ^ 59
def prefixEnd_3681344 : Nat := 4983230072969 + 3 ^ 40 * 3681344 * 2
def baseEnd_3681344 : Nat := 1890298926545349958369813

theorem tailTrace_3681344 : CollatzResearch.WordTrace tailWord_3681344 prefixEnd_3681344 1890298926545349958369813 := by
  unfold tailWord_3681344
  simp only [CollatzResearch.WordTrace]
  refine ⟨67134823187563443172537543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89513097583417924230050057 67134823187563443172537543)
  ·
    refine ⟨100702234781345164758806315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67134823187563443172537543 100702234781345164758806315)
    ·
      refine ⟨151053352172017747138209473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100702234781345164758806315 151053352172017747138209473)
      ·
        refine ⟨113290014129013310353657105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151053352172017747138209473 113290014129013310353657105)
        ·
          refine ⟨84967510596759982765242829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113290014129013310353657105 84967510596759982765242829)
          ·
            refine ⟨31862816473784993536966061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84967510596759982765242829 31862816473784993536966061)
            ·
              refine ⟨11948556177669372576362273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31862816473784993536966061 11948556177669372576362273)
              ·
                refine ⟨8961417133252029432271705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11948556177669372576362273 8961417133252029432271705)
                ·
                  refine ⟨6721062849939022074203779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8961417133252029432271705 6721062849939022074203779)
                  ·
                    refine ⟨10081594274908533111305669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6721062849939022074203779 10081594274908533111305669)
                    ·
                      refine ⟨1890298926545349958369813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10081594274908533111305669 1890298926545349958369813)
                      ·
                        rfl

theorem cell23_3681344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_3681344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681344 prefixEnd_3681344 := by exact prefixLift 3681344
  have htrace : WordTrace (prefixWord ++ tailWord_3681344) baseStart_3681344 baseEnd_3681344 := by
    simpa [prefixWord, tailWord_3681344, baseEnd_3681344] using wordTrace_append hprefix tailTrace_3681344
  have hstable : (prefixWord ++ tailWord_3681344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681344).length < 2 ^ (prefixWord ++ tailWord_3681344).sum := by decide
  have hdescent : baseEnd_3681344 < baseStart_3681344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681364 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_3681364 : Nat := 118140960795 + 3681364 * 2 ^ 59
def prefixEnd_3681364 : Nat := 4983230072969 + 3 ^ 40 * 3681364 * 2
def baseEnd_3681364 : Nat := 1890309196158439880119721

theorem tailTrace_3681364 : CollatzResearch.WordTrace tailWord_3681364 prefixEnd_3681364 1890309196158439880119721 := by
  unfold tailWord_3681364
  simp only [CollatzResearch.WordTrace]
  refine ⟨67135187917527214880401573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89513583890036286507202097 67135187917527214880401573)
  ·
    refine ⟨12587847734536352790075295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67135187917527214880401573 12587847734536352790075295)
    ·
      refine ⟨18881771601804529185112943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12587847734536352790075295 18881771601804529185112943)
      ·
        refine ⟨28322657402706793777669415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18881771601804529185112943 28322657402706793777669415)
        ·
          refine ⟨42483986104060190666504123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28322657402706793777669415 42483986104060190666504123)
          ·
            refine ⟨63725979156090285999756185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42483986104060190666504123 63725979156090285999756185)
            ·
              refine ⟨47794484367067714499817139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63725979156090285999756185 47794484367067714499817139)
              ·
                refine ⟨71691726550601571749725709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47794484367067714499817139 71691726550601571749725709)
                ·
                  refine ⟨26884397456475589406147141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71691726550601571749725709 26884397456475589406147141)
                  ·
                    refine ⟨5040824523089173013652589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26884397456475589406147141 5040824523089173013652589)
                    ·
                      refine ⟨1890309196158439880119721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5040824523089173013652589 1890309196158439880119721)
                      ·
                        rfl

theorem cell23_3681364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_3681364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681364 prefixEnd_3681364 := by exact prefixLift 3681364
  have htrace : WordTrace (prefixWord ++ tailWord_3681364) baseStart_3681364 baseEnd_3681364 := by
    simpa [prefixWord, tailWord_3681364, baseEnd_3681364] using wordTrace_append hprefix tailTrace_3681364
  have hstable : (prefixWord ++ tailWord_3681364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681364).length < 2 ^ (prefixWord ++ tailWord_3681364).sum := by decide
  have hdescent : baseEnd_3681364 < baseStart_3681364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681378 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3681378 : Nat := 118140960795 + 3681378 * 2 ^ 59
def prefixEnd_3681378 : Nat := 4983230072969 + 3 ^ 40 * 3681378 * 2
def baseEnd_3681378 : Nat := 1890316384887602825344657

theorem tailTrace_3681378 : CollatzResearch.WordTrace tailWord_3681378 prefixEnd_3681378 1890316384887602825344657 := by
  unfold tailWord_3681378
  simp only [CollatzResearch.WordTrace]
  refine ⟨33567721614250927537953197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89513924304669140101208525 33567721614250927537953197)
  ·
    refine ⟨12587895605344097826732449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33567721614250927537953197 12587895605344097826732449)
    ·
      refine ⟨9440921704008073370049337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12587895605344097826732449 9440921704008073370049337)
      ·
        refine ⟨7080691278006055027537003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9440921704008073370049337 7080691278006055027537003)
        ·
          refine ⟨10621036917009082541305505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7080691278006055027537003 10621036917009082541305505)
          ·
            refine ⟨7965777687756811905979129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10621036917009082541305505 7965777687756811905979129)
            ·
              refine ⟨5974333265817608929484347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7965777687756811905979129 5974333265817608929484347)
              ·
                refine ⟨8961499898726413394226521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5974333265817608929484347 8961499898726413394226521)
                ·
                  refine ⟨6721124924044810045669891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8961499898726413394226521 6721124924044810045669891)
                  ·
                    refine ⟨10081687386067215068504837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6721124924044810045669891 10081687386067215068504837)
                    ·
                      refine ⟨1890316384887602825344657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10081687386067215068504837 1890316384887602825344657)
                      ·
                        rfl

theorem cell23_3681378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3681378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681378 prefixEnd_3681378 := by exact prefixLift 3681378
  have htrace : WordTrace (prefixWord ++ tailWord_3681378) baseStart_3681378 baseEnd_3681378 := by
    simpa [prefixWord, tailWord_3681378, baseEnd_3681378] using wordTrace_append hprefix tailTrace_3681378
  have hstable : (prefixWord ++ tailWord_3681378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681378).length < 2 ^ (prefixWord ++ tailWord_3681378).sum := by decide
  have hdescent : baseEnd_3681378 < baseStart_3681378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681381 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 2, 2, 3]
def baseStart_3681381 : Nat := 118140960795 + 3681381 * 2 ^ 59
def prefixEnd_3681381 : Nat := 4983230072969 + 3 ^ 40 * 3681381 * 2
def baseEnd_3681381 : Nat := 1890317925329566313607143

theorem tailTrace_3681381 : CollatzResearch.WordTrace tailWord_3681381 prefixEnd_3681381 1890317925329566313607143 := by
  unfold tailWord_3681381
  simp only [CollatzResearch.WordTrace]
  refine ⟨134270995875992841664171997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89513997250661894442781331 134270995875992841664171997)
  ·
    refine ⟨50351623453497315624064499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134270995875992841664171997 50351623453497315624064499)
    ·
      refine ⟨75527435180245973436096749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50351623453497315624064499 75527435180245973436096749)
      ·
        refine ⟨28322788192592240038536281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75527435180245973436096749 28322788192592240038536281)
        ·
          refine ⟨21242091144444180028902211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28322788192592240038536281 21242091144444180028902211)
          ·
            refine ⟨31863136716666270043353317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21242091144444180028902211 31863136716666270043353317)
            ·
              refine ⟨5974338134374925633128747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31863136716666270043353317 5974338134374925633128747)
              ·
                refine ⟨8961507201562388449693121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5974338134374925633128747 8961507201562388449693121)
                ·
                  refine ⟨6721130401171791337269841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8961507201562388449693121 6721130401171791337269841)
                  ·
                    refine ⟨5040847800878843502952381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6721130401171791337269841 5040847800878843502952381)
                    ·
                      refine ⟨1890317925329566313607143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5040847800878843502952381 1890317925329566313607143)
                      ·
                        rfl

theorem cell23_3681381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_3681381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681381 prefixEnd_3681381 := by exact prefixLift 3681381
  have htrace : WordTrace (prefixWord ++ tailWord_3681381) baseStart_3681381 baseEnd_3681381 := by
    simpa [prefixWord, tailWord_3681381, baseEnd_3681381] using wordTrace_append hprefix tailTrace_3681381
  have hstable : (prefixWord ++ tailWord_3681381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681381).length < 2 ^ (prefixWord ++ tailWord_3681381).sum := by decide
  have hdescent : baseEnd_3681381 < baseStart_3681381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681401 : List Nat := [1, 2, 1, 3, 5, 1, 2, 2, 6]
def baseStart_3681401 : Nat := 118140960795 + 3681401 * 2 ^ 59
def prefixEnd_3681401 : Nat := 4983230072969 + 3 ^ 40 * 3681401 * 2
def baseEnd_3681401 : Nat := 210036466104739581706339

theorem tailTrace_3681401 : CollatzResearch.WordTrace tailWord_3681401 prefixEnd_3681401 210036466104739581706339 := by
  unfold tailWord_3681401
  simp only [CollatzResearch.WordTrace]
  refine ⟨134271725335920385079900057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89514483557280256719933371 134271725335920385079900057)
  ·
    refine ⟨100703794001940288809925043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134271725335920385079900057 100703794001940288809925043)
    ·
      refine ⟨151055691002910433214887565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100703794001940288809925043 151055691002910433214887565)
      ·
        refine ⟨56645884126091412455582837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151055691002910433214887565 56645884126091412455582837)
        ·
          refine ⟨5310551636821069917710891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56645884126091412455582837 5310551636821069917710891)
          ·
            refine ⟨7965827455231604876566337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5310551636821069917710891 7965827455231604876566337)
            ·
              refine ⟨5974370591423703657424753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7965827455231604876566337 5974370591423703657424753)
              ·
                refine ⟨4480777943567777743068565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5974370591423703657424753 4480777943567777743068565)
                ·
                  refine ⟨210036466104739581706339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4480777943567777743068565 210036466104739581706339)
                  ·
                    rfl

theorem cell23_3681401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 2, 6].length) (baseStart_3681401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681401 prefixEnd_3681401 := by exact prefixLift 3681401
  have htrace : WordTrace (prefixWord ++ tailWord_3681401) baseStart_3681401 baseEnd_3681401 := by
    simpa [prefixWord, tailWord_3681401, baseEnd_3681401] using wordTrace_append hprefix tailTrace_3681401
  have hstable : (prefixWord ++ tailWord_3681401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681401).length < 2 ^ (prefixWord ++ tailWord_3681401).sum := by decide
  have hdescent : baseEnd_3681401 < baseStart_3681401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681407 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 5]
def baseStart_3681407 : Nat := 118140960795 + 3681407 * 2 ^ 59
def prefixEnd_3681407 : Nat := 4983230072969 + 3 ^ 40 * 3681407 * 2
def baseEnd_3681407 : Nat := 1890331275826583211882023

theorem tailTrace_3681407 : CollatzResearch.WordTrace tailWord_3681407 prefixEnd_3681407 1890331275826583211882023 := by
  unfold tailWord_3681407
  simp only [CollatzResearch.WordTrace]
  refine ⟨134271944173898648104618475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89514629449265765403078983 134271944173898648104618475)
  ·
    refine ⟨201407916260847972156927713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134271944173898648104618475 201407916260847972156927713)
    ·
      refine ⟨151055937195635979117695785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201407916260847972156927713 151055937195635979117695785)
      ·
        refine ⟨113291952896726984338271839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151055937195635979117695785 113291952896726984338271839)
        ·
          refine ⟨169937929345090476507407759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113291952896726984338271839 169937929345090476507407759)
          ·
            refine ⟨254906894017635714761111639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169937929345090476507407759 254906894017635714761111639)
            ·
              refine ⟨382360341026453572141667459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254906894017635714761111639 382360341026453572141667459)
              ·
                refine ⟨573540511539680358212501189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382360341026453572141667459 573540511539680358212501189)
                ·
                  refine ⟨107538845913690067164843973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 573540511539680358212501189 107538845913690067164843973)
                  ·
                    refine ⟨20163533608816887593408245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107538845913690067164843973 20163533608816887593408245)
                    ·
                      refine ⟨1890331275826583211882023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20163533608816887593408245 1890331275826583211882023)
                      ·
                        rfl

theorem cell23_3681407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_3681407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681407 prefixEnd_3681407 := by exact prefixLift 3681407
  have htrace : WordTrace (prefixWord ++ tailWord_3681407) baseStart_3681407 baseEnd_3681407 := by
    simpa [prefixWord, tailWord_3681407, baseEnd_3681407] using wordTrace_append hprefix tailTrace_3681407
  have hstable : (prefixWord ++ tailWord_3681407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681407).length < 2 ^ (prefixWord ++ tailWord_3681407).sum := by decide
  have hdescent : baseEnd_3681407 < baseStart_3681407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681411 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 3, 1, 3]
def baseStart_3681411 : Nat := 118140960795 + 3681411 * 2 ^ 59
def prefixEnd_3681411 : Nat := 4983230072969 + 3 ^ 40 * 3681411 * 2
def baseEnd_3681411 : Nat := 1890333329749201196232005

theorem tailTrace_3681411 : CollatzResearch.WordTrace tailWord_3681411 prefixEnd_3681411 1890333329749201196232005 := by
  unfold tailWord_3681411
  simp only [CollatzResearch.WordTrace]
  refine ⟨134272090065884156787764087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89514726710589437858509391 134272090065884156787764087)
  ·
    refine ⟨201408135098826235181646131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134272090065884156787764087 201408135098826235181646131)
    ·
      refine ⟨302112202648239352772469197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201408135098826235181646131 302112202648239352772469197)
      ·
        refine ⟨113292075993089757289675949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302112202648239352772469197 113292075993089757289675949)
        ·
          refine ⟨42484528497408658983628481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113292075993089757289675949 42484528497408658983628481)
          ·
            refine ⟨31863396373056494237721361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42484528497408658983628481 31863396373056494237721361)
            ·
              refine ⟨23897547279792370678291021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31863396373056494237721361 23897547279792370678291021)
              ·
                refine ⟨8961580229922139004359133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23897547279792370678291021 8961580229922139004359133)
                ·
                  refine ⟨3360592586220802126634675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8961580229922139004359133 3360592586220802126634675)
                  ·
                    refine ⟨5040888879331203189952013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3360592586220802126634675 5040888879331203189952013)
                    ·
                      refine ⟨1890333329749201196232005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5040888879331203189952013 1890333329749201196232005)
                      ·
                        rfl

theorem cell23_3681411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_3681411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681411 prefixEnd_3681411 := by exact prefixLift 3681411
  have htrace : WordTrace (prefixWord ++ tailWord_3681411) baseStart_3681411 baseEnd_3681411 := by
    simpa [prefixWord, tailWord_3681411, baseEnd_3681411] using wordTrace_append hprefix tailTrace_3681411
  have hstable : (prefixWord ++ tailWord_3681411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681411).length < 2 ^ (prefixWord ++ tailWord_3681411).sum := by decide
  have hdescent : baseEnd_3681411 < baseStart_3681411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681445 : List Nat := [1, 3, 1, 2, 1, 5, 2, 3, 1, 1, 3]
def baseStart_3681445 : Nat := 118140960795 + 3681445 * 2 ^ 59
def prefixEnd_3681445 : Nat := 4983230072969 + 3 ^ 40 * 3681445 * 2
def baseEnd_3681445 : Nat := 1890350788091454063206849

theorem tailTrace_3681445 : CollatzResearch.WordTrace tailWord_3681445 prefixEnd_3681445 1890350788091454063206849 := by
  unfold tailWord_3681445
  simp only [CollatzResearch.WordTrace]
  refine ⟨134273330147760980594501789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89515553431840653729667859 134273330147760980594501789)
  ·
    refine ⟨50352498805410367722938171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134273330147760980594501789 50352498805410367722938171)
    ·
      refine ⟨75528748208115551584407257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50352498805410367722938171 75528748208115551584407257)
      ·
        refine ⟨56646561156086663688305443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75528748208115551584407257 56646561156086663688305443)
        ·
          refine ⟨84969841734129995532458165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56646561156086663688305443 84969841734129995532458165)
          ·
            refine ⟨7965922662574687081167953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84969841734129995532458165 7965922662574687081167953)
            ·
              refine ⟨5974441996931015310875965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7965922662574687081167953 5974441996931015310875965)
              ·
                refine ⟨2240415748849130741578487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5974441996931015310875965 2240415748849130741578487)
                ·
                  refine ⟨3360623623273696112367731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2240415748849130741578487 3360623623273696112367731)
                  ·
                    refine ⟨5040935434910544168551597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3360623623273696112367731 5040935434910544168551597)
                    ·
                      refine ⟨1890350788091454063206849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5040935434910544168551597 1890350788091454063206849)
                      ·
                        rfl

theorem cell23_3681445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_3681445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681445 prefixEnd_3681445 := by exact prefixLift 3681445
  have htrace : WordTrace (prefixWord ++ tailWord_3681445) baseStart_3681445 baseEnd_3681445 := by
    simpa [prefixWord, tailWord_3681445, baseEnd_3681445] using wordTrace_append hprefix tailTrace_3681445
  have hstable : (prefixWord ++ tailWord_3681445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681445).length < 2 ^ (prefixWord ++ tailWord_3681445).sum := by decide
  have hdescent : baseEnd_3681445 < baseStart_3681445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681518 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 4, 1, 3]
def baseStart_3681518 : Nat := 118140960795 + 3681518 * 2 ^ 59
def prefixEnd_3681518 : Nat := 4983230072969 + 3 ^ 40 * 3681518 * 2
def baseEnd_3681518 : Nat := 1890388272179232277594013

theorem tailTrace_3681518 : CollatzResearch.WordTrace tailWord_3681518 prefixEnd_3681518 1890388272179232277594013 := by
  unfold tailWord_3681518
  simp only [CollatzResearch.WordTrace]
  refine ⟨16784499084562064257738651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89517328450997676041272805 16784499084562064257738651)
  ·
    refine ⟨25176748626843096386607977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16784499084562064257738651 25176748626843096386607977)
    ·
      refine ⟨18882561470132322289955983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25176748626843096386607977 18882561470132322289955983)
      ·
        refine ⟨28323842205198483434933975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18882561470132322289955983 28323842205198483434933975)
        ·
          refine ⟨42485763307797725152400963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28323842205198483434933975 42485763307797725152400963)
          ·
            refine ⟨63728644961696587728601445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42485763307797725152400963 63728644961696587728601445)
            ·
              refine ⟨11949120930318110199112771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63728644961696587728601445 11949120930318110199112771)
              ·
                refine ⟨17923681395477165298669157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11949120930318110199112771 17923681395477165298669157)
                ·
                  refine ⟨3360690261651968493500467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17923681395477165298669157 3360690261651968493500467)
                  ·
                    refine ⟨5041035392477952740250701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3360690261651968493500467 5041035392477952740250701)
                    ·
                      refine ⟨1890388272179232277594013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5041035392477952740250701 1890388272179232277594013)
                      ·
                        rfl

theorem cell23_3681518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_3681518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681518 prefixEnd_3681518 := by exact prefixLift 3681518
  have htrace : WordTrace (prefixWord ++ tailWord_3681518) baseStart_3681518 baseEnd_3681518 := by
    simpa [prefixWord, tailWord_3681518, baseEnd_3681518] using wordTrace_append hprefix tailTrace_3681518
  have hstable : (prefixWord ++ tailWord_3681518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681518).length < 2 ^ (prefixWord ++ tailWord_3681518).sum := by decide
  have hdescent : baseEnd_3681518 < baseStart_3681518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681519 : List Nat := [1, 1, 2, 1, 7, 1, 3, 2, 1, 2, 2]
def baseStart_3681519 : Nat := 118140960795 + 3681519 * 2 ^ 59
def prefixEnd_3681519 : Nat := 4983230072969 + 3 ^ 40 * 3681519 * 2
def baseEnd_3681519 : Nat := 1890388785659886773681509

theorem tailTrace_3681519 : CollatzResearch.WordTrace tailWord_3681519 prefixEnd_3681519 1890388785659886773681509 := by
  unfold tailWord_3681519
  simp only [CollatzResearch.WordTrace]
  refine ⟨134276029149492891232695611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89517352766328594155130407 134276029149492891232695611)
  ·
    refine ⟨201414043724239336849043417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134276029149492891232695611 201414043724239336849043417)
    ·
      refine ⟨151060532793179502636782563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201414043724239336849043417 151060532793179502636782563)
      ·
        refine ⟨226590799189769253955173845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151060532793179502636782563 226590799189769253955173845)
        ·
          refine ⟨5310721856010216889574387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 226590799189769253955173845 5310721856010216889574387)
          ·
            refine ⟨7966082784015325334361581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5310721856010216889574387 7966082784015325334361581)
            ·
              refine ⟨2987281044005747000385593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7966082784015325334361581 2987281044005747000385593)
              ·
                refine ⟨2240460783004310250289195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2987281044005747000385593 2240460783004310250289195)
                ·
                  refine ⟨3360691174506465375433793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2240460783004310250289195 3360691174506465375433793)
                  ·
                    refine ⟨2520518380879849031575345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3360691174506465375433793 2520518380879849031575345)
                    ·
                      refine ⟨1890388785659886773681509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2520518380879849031575345 1890388785659886773681509)
                      ·
                        rfl

theorem cell23_3681519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 2, 1, 2, 2].length) (baseStart_3681519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681519 prefixEnd_3681519 := by exact prefixLift 3681519
  have htrace : WordTrace (prefixWord ++ tailWord_3681519) baseStart_3681519 baseEnd_3681519 := by
    simpa [prefixWord, tailWord_3681519, baseEnd_3681519] using wordTrace_append hprefix tailTrace_3681519
  have hstable : (prefixWord ++ tailWord_3681519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681519).length < 2 ^ (prefixWord ++ tailWord_3681519).sum := by decide
  have hdescent : baseEnd_3681519 < baseStart_3681519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681535 : List Nat := [1, 1, 2, 2, 1, 5, 4, 1, 2, 1, 3]
def baseStart_3681535 : Nat := 118140960795 + 3681535 * 2 ^ 59
def prefixEnd_3681535 : Nat := 4983230072969 + 3 ^ 40 * 3681535 * 2
def baseEnd_3681535 : Nat := 1890397001350358711081435

theorem tailTrace_3681535 : CollatzResearch.WordTrace tailWord_3681535 prefixEnd_3681535 1890397001350358711081435 := by
  unfold tailWord_3681535
  simp only [CollatzResearch.WordTrace]
  refine ⟨134276612717434925965278059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89517741811623283976852039 134276612717434925965278059)
  ·
    refine ⟨201414919076152388947917089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134276612717434925965278059 201414919076152388947917089)
    ·
      refine ⟨151061189307114291710937817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201414919076152388947917089 151061189307114291710937817)
      ·
        refine ⟨113295891980335718783203363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151061189307114291710937817 113295891980335718783203363)
        ·
          refine ⟨169943837970503578174805045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113295891980335718783203363 169943837970503578174805045)
          ·
            refine ⟨15932234809734710453887973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169943837970503578174805045 15932234809734710453887973)
            ·
              refine ⟨2987294026825258210103995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15932234809734710453887973 2987294026825258210103995)
              ·
                refine ⟨4480941040237887315155993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987294026825258210103995 4480941040237887315155993)
                ·
                  refine ⟨3360705780178415486366995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4480941040237887315155993 3360705780178415486366995)
                  ·
                    refine ⟨5041058670267623229550493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3360705780178415486366995 5041058670267623229550493)
                    ·
                      refine ⟨1890397001350358711081435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5041058670267623229550493 1890397001350358711081435)
                      ·
                        rfl

theorem cell23_3681535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 2, 1, 3].length) (baseStart_3681535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681535 prefixEnd_3681535 := by exact prefixLift 3681535
  have htrace : WordTrace (prefixWord ++ tailWord_3681535) baseStart_3681535 baseEnd_3681535 := by
    simpa [prefixWord, tailWord_3681535, baseEnd_3681535] using wordTrace_append hprefix tailTrace_3681535
  have hstable : (prefixWord ++ tailWord_3681535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681535).length < 2 ^ (prefixWord ++ tailWord_3681535).sum := by decide
  have hdescent : baseEnd_3681535 < baseStart_3681535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681562 : List Nat := [3, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2]
def baseStart_3681562 : Nat := 118140960795 + 3681562 * 2 ^ 59
def prefixEnd_3681562 : Nat := 4983230072969 + 3 ^ 40 * 3681562 * 2
def baseEnd_3681562 : Nat := 1890410865328030105443811

theorem tailTrace_3681562 : CollatzResearch.WordTrace tailWord_3681562 prefixEnd_3681562 1890410865328030105443811 := by
  unfold tailWord_3681562
  simp only [CollatzResearch.WordTrace]
  refine ⟨33569399372084277394127735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89518398325558073051007293 33569399372084277394127735)
  ·
    refine ⟨50354099058126416091191603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33569399372084277394127735 50354099058126416091191603)
    ·
      refine ⟨75531148587189624136787405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50354099058126416091191603 75531148587189624136787405)
      ·
        refine ⟨28324180720196109051295277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75531148587189624136787405 28324180720196109051295277)
        ·
          refine ⟨10621567770073540894235729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28324180720196109051295277 10621567770073540894235729)
          ·
            refine ⟨7966175827555155670676797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10621567770073540894235729 7966175827555155670676797)
            ·
              refine ⟨2987315935333183376503799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7966175827555155670676797 2987315935333183376503799)
              ·
                refine ⟨4480973902999775064755699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987315935333183376503799 4480973902999775064755699)
                ·
                  refine ⟨6721460854499662597133549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4480973902999775064755699 6721460854499662597133549)
                  ·
                    refine ⟨2520547820437373473925081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6721460854499662597133549 2520547820437373473925081)
                    ·
                      refine ⟨1890410865328030105443811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2520547820437373473925081 1890410865328030105443811)
                      ·
                        rfl

theorem cell23_3681562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_3681562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681562 prefixEnd_3681562 := by exact prefixLift 3681562
  have htrace : WordTrace (prefixWord ++ tailWord_3681562) baseStart_3681562 baseEnd_3681562 := by
    simpa [prefixWord, tailWord_3681562, baseEnd_3681562] using wordTrace_append hprefix tailTrace_3681562
  have hstable : (prefixWord ++ tailWord_3681562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681562).length < 2 ^ (prefixWord ++ tailWord_3681562).sum := by decide
  have hdescent : baseEnd_3681562 < baseStart_3681562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681578 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_3681578 : Nat := 118140960795 + 3681578 * 2 ^ 59
def prefixEnd_3681578 : Nat := 4983230072969 + 3 ^ 40 * 3681578 * 2
def baseEnd_3681578 : Nat := 1890419081018502042843737

theorem tailTrace_3681578 : CollatzResearch.WordTrace tailWord_3681578 prefixEnd_3681578 1890419081018502042843737 := by
  unfold tailWord_3681578
  simp only [CollatzResearch.WordTrace]
  refine ⟨33569545264069786077273347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89518787370852762872728925 33569545264069786077273347)
  ·
    refine ⟨50354317896104679115910021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33569545264069786077273347 50354317896104679115910021)
    ·
      refine ⟨9441434605519627334233129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50354317896104679115910021 9441434605519627334233129)
      ·
        refine ⟨7081075954139720500674847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9441434605519627334233129 7081075954139720500674847)
        ·
          refine ⟨10621613931209580751012271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7081075954139720500674847 10621613931209580751012271)
          ·
            refine ⟨15932420896814371126518407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10621613931209580751012271 15932420896814371126518407)
            ·
              refine ⟨23898631345221556689777611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15932420896814371126518407 23898631345221556689777611)
              ·
                refine ⟨35847947017832335034666417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23898631345221556689777611 35847947017832335034666417)
                ·
                  refine ⟨26885960263374251275999813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35847947017832335034666417 26885960263374251275999813)
                  ·
                    refine ⟨5041117549382672114249965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26885960263374251275999813 5041117549382672114249965)
                    ·
                      refine ⟨1890419081018502042843737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5041117549382672114249965 1890419081018502042843737)
                      ·
                        rfl

theorem cell23_3681578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_3681578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681578 prefixEnd_3681578 := by exact prefixLift 3681578
  have htrace : WordTrace (prefixWord ++ tailWord_3681578) baseStart_3681578 baseEnd_3681578 := by
    simpa [prefixWord, tailWord_3681578, baseEnd_3681578] using wordTrace_append hprefix tailTrace_3681578
  have hstable : (prefixWord ++ tailWord_3681578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681578).length < 2 ^ (prefixWord ++ tailWord_3681578).sum := by decide
  have hdescent : baseEnd_3681578 < baseStart_3681578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681588 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_3681588 : Nat := 118140960795 + 3681588 * 2 ^ 59
def prefixEnd_3681588 : Nat := 4983230072969 + 3 ^ 40 * 3681588 * 2
def baseEnd_3681588 : Nat := 1890424215825047003718691

theorem tailTrace_3681588 : CollatzResearch.WordTrace tailWord_3681588 prefixEnd_3681588 1890424215825047003718691 := by
  unfold tailWord_3681588
  simp only [CollatzResearch.WordTrace]
  refine ⟨67139272893121458008478709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89519030524161944011304945 67139272893121458008478709)
  ·
    refine ⟨6294306833730136688294879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67139272893121458008478709 6294306833730136688294879)
    ·
      refine ⟨9441460250595205032442319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6294306833730136688294879 9441460250595205032442319)
      ·
        refine ⟨14162190375892807548663479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9441460250595205032442319 14162190375892807548663479)
        ·
          refine ⟨21243285563839211322995219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14162190375892807548663479 21243285563839211322995219)
          ·
            refine ⟨31864928345758816984492829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21243285563839211322995219 31864928345758816984492829)
            ·
              refine ⟨11949348129659556369184811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31864928345758816984492829 11949348129659556369184811)
              ·
                refine ⟨17924022194489334553777217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11949348129659556369184811 17924022194489334553777217)
                ·
                  refine ⟨13443016645867000915332913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17924022194489334553777217 13443016645867000915332913)
                  ·
                    refine ⟨10082262484400250686499685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13443016645867000915332913 10082262484400250686499685)
                    ·
                      refine ⟨1890424215825047003718691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10082262484400250686499685 1890424215825047003718691)
                      ·
                        rfl

theorem cell23_3681588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_3681588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681588 prefixEnd_3681588 := by exact prefixLift 3681588
  have htrace : WordTrace (prefixWord ++ tailWord_3681588) baseStart_3681588 baseEnd_3681588 := by
    simpa [prefixWord, tailWord_3681588, baseEnd_3681588] using wordTrace_append hprefix tailTrace_3681588
  have hstable : (prefixWord ++ tailWord_3681588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681588).length < 2 ^ (prefixWord ++ tailWord_3681588).sum := by decide
  have hdescent : baseEnd_3681588 < baseStart_3681588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681613 : List Nat := [1, 6, 1, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_3681613 : Nat := 118140960795 + 3681613 * 2 ^ 59
def prefixEnd_3681613 : Nat := 4983230072969 + 3 ^ 40 * 3681613 * 2
def baseEnd_3681613 : Nat := 1890437052841409405906077

theorem tailTrace_3681613 : CollatzResearch.WordTrace tailWord_3681613 prefixEnd_3681613 1890437052841409405906077 := by
  unfold tailWord_3681613
  simp only [CollatzResearch.WordTrace]
  refine ⟨134279457611152345286617493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89519638407434896857744995 134279457611152345286617493)
  ·
    refine ⟨6294349575522766185310195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134279457611152345286617493 6294349575522766185310195)
    ·
      refine ⟨9441524363284149277965293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6294349575522766185310195 9441524363284149277965293)
      ·
        refine ⟨3540571636231555979236985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9441524363284149277965293 3540571636231555979236985)
        ·
          refine ⟨2655428727173666984427739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3540571636231555979236985 2655428727173666984427739)
          ·
            refine ⟨3983143090760500476641609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655428727173666984427739 3983143090760500476641609)
            ·
              refine ⟨2987357318070375357481207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3983143090760500476641609 2987357318070375357481207)
              ·
                refine ⟨4481035977105563036221811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987357318070375357481207 4481035977105563036221811)
                ·
                  refine ⟨6721553965658344554332717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4481035977105563036221811 6721553965658344554332717)
                  ·
                    refine ⟨2520582737121879207874769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6721553965658344554332717 2520582737121879207874769)
                    ·
                      refine ⟨1890437052841409405906077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2520582737121879207874769 1890437052841409405906077)
                      ·
                        rfl

theorem cell23_3681613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_3681613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681613 prefixEnd_3681613 := by exact prefixLift 3681613
  have htrace : WordTrace (prefixWord ++ tailWord_3681613) baseStart_3681613 baseEnd_3681613 := by
    simpa [prefixWord, tailWord_3681613, baseEnd_3681613] using wordTrace_append hprefix tailTrace_3681613
  have hstable : (prefixWord ++ tailWord_3681613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681613).length < 2 ^ (prefixWord ++ tailWord_3681613).sum := by decide
  have hdescent : baseEnd_3681613 < baseStart_3681613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681631 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 4]
def baseStart_3681631 : Nat := 118140960795 + 3681631 * 2 ^ 59
def prefixEnd_3681631 : Nat := 4983230072969 + 3 ^ 40 * 3681631 * 2
def baseEnd_3681631 : Nat := 1890446295493190335480993

theorem tailTrace_3681631 : CollatzResearch.WordTrace tailWord_3681631 prefixEnd_3681631 1890446295493190335480993 := by
  unfold tailWord_3681631
  simp only [CollatzResearch.WordTrace]
  refine ⟨134280114125087134360772747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89520076083391422907181831 134280114125087134360772747)
  ·
    refine ⟨201420171187630701541159121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134280114125087134360772747 201420171187630701541159121)
    ·
      refine ⟨151065128390723026155869341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201420171187630701541159121 151065128390723026155869341)
      ·
        refine ⟨56649423146521134808451003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151065128390723026155869341 56649423146521134808451003)
        ·
          refine ⟨84974134719781702212676505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56649423146521134808451003 84974134719781702212676505)
          ·
            refine ⟨63730601039836276659507379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84974134719781702212676505 63730601039836276659507379)
            ·
              refine ⟨95595901559754414989261069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63730601039836276659507379 95595901559754414989261069)
              ·
                refine ⟨35848463084907905620972901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95595901559754414989261069 35848463084907905620972901)
                ·
                  refine ⟨6721586828420232303932419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35848463084907905620972901 6721586828420232303932419)
                  ·
                    refine ⟨10082380242630348455898629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6721586828420232303932419 10082380242630348455898629)
                    ·
                      refine ⟨1890446295493190335480993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10082380242630348455898629 1890446295493190335480993)
                      ·
                        rfl

theorem cell23_3681631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_3681631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681631 prefixEnd_3681631 := by exact prefixLift 3681631
  have htrace : WordTrace (prefixWord ++ tailWord_3681631) baseStart_3681631 baseEnd_3681631 := by
    simpa [prefixWord, tailWord_3681631, baseEnd_3681631] using wordTrace_append hprefix tailTrace_3681631
  have hstable : (prefixWord ++ tailWord_3681631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681631).length < 2 ^ (prefixWord ++ tailWord_3681631).sum := by decide
  have hdescent : baseEnd_3681631 < baseStart_3681631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681648 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 2, 4, 2]
def baseStart_3681648 : Nat := 118140960795 + 3681648 * 2 ^ 59
def prefixEnd_3681648 : Nat := 4983230072969 + 3 ^ 40 * 3681648 * 2
def baseEnd_3681648 : Nat := 1890455024664316768968415

theorem tailTrace_3681648 : CollatzResearch.WordTrace tailWord_3681648 prefixEnd_3681648 1890455024664316768968415 := by
  unfold tailWord_3681648
  simp only [CollatzResearch.WordTrace]
  refine ⟨67140367083012773132070799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89520489444017030842761065 67140367083012773132070799)
  ·
    refine ⟨100710550624519159698106199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67140367083012773132070799 100710550624519159698106199)
    ·
      refine ⟨151065825936778739547159299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100710550624519159698106199 151065825936778739547159299)
      ·
        refine ⟨226598738905168109320738949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151065825936778739547159299 226598738905168109320738949)
        ·
          refine ⟨42487263544719020497638553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226598738905168109320738949 42487263544719020497638553)
          ·
            refine ⟨31865447658539265373228915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42487263544719020497638553 31865447658539265373228915)
            ·
              refine ⟨47798171487808898059843373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31865447658539265373228915 47798171487808898059843373)
              ·
                refine ⟨17924314307928336772441265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47798171487808898059843373 17924314307928336772441265)
                ·
                  refine ⟨13443235730946252579330949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17924314307928336772441265 13443235730946252579330949)
                  ·
                    refine ⟨2520606699552422358624553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13443235730946252579330949 2520606699552422358624553)
                    ·
                      refine ⟨1890455024664316768968415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2520606699552422358624553 1890455024664316768968415)
                      ·
                        rfl

theorem cell23_3681648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 2, 4, 2].length) (baseStart_3681648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681648 prefixEnd_3681648 := by exact prefixLift 3681648
  have htrace : WordTrace (prefixWord ++ tailWord_3681648) baseStart_3681648 baseEnd_3681648 := by
    simpa [prefixWord, tailWord_3681648, baseEnd_3681648] using wordTrace_append hprefix tailTrace_3681648
  have hstable : (prefixWord ++ tailWord_3681648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681648).length < 2 ^ (prefixWord ++ tailWord_3681648).sum := by decide
  have hdescent : baseEnd_3681648 < baseStart_3681648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681661 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_3681661 : Nat := 118140960795 + 3681661 * 2 ^ 59
def prefixEnd_3681661 : Nat := 4983230072969 + 3 ^ 40 * 3681661 * 2
def baseEnd_3681661 : Nat := 1890461699912825218105855

theorem tailTrace_3681661 : CollatzResearch.WordTrace tailWord_3681661 prefixEnd_3681661 1890461699912825218105855 := by
  unfold tailWord_3681661
  simp only [CollatzResearch.WordTrace]
  refine ⟨134281208314978449484364837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89520805543318966322909891 134281208314978449484364837)
  ·
    refine ⟨25177726559058459278318407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134281208314978449484364837 25177726559058459278318407)
    ·
      refine ⟨37766589838587688917477611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25177726559058459278318407 37766589838587688917477611)
      ·
        refine ⟨56649884757881533376216417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37766589838587688917477611 56649884757881533376216417)
        ·
          refine ⟨42487413568411150032162313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56649884757881533376216417 42487413568411150032162313)
          ·
            refine ⟨31865560176308362524121735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42487413568411150032162313 31865560176308362524121735)
            ·
              refine ⟨47798340264462543786182603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31865560176308362524121735 47798340264462543786182603)
              ·
                refine ⟨71697510396693815679273905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47798340264462543786182603 71697510396693815679273905)
                ·
                  refine ⟨53773132797520361759455429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71697510396693815679273905 53773132797520361759455429)
                  ·
                    refine ⟨10082462399535067829897893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53773132797520361759455429 10082462399535067829897893)
                    ·
                      refine ⟨1890461699912825218105855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10082462399535067829897893 1890461699912825218105855)
                      ·
                        rfl

theorem cell23_3681661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_3681661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681661 prefixEnd_3681661 := by exact prefixLift 3681661
  have htrace : WordTrace (prefixWord ++ tailWord_3681661) baseStart_3681661 baseEnd_3681661 := by
    simpa [prefixWord, tailWord_3681661, baseEnd_3681661] using wordTrace_append hprefix tailTrace_3681661
  have hstable : (prefixWord ++ tailWord_3681661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681661).length < 2 ^ (prefixWord ++ tailWord_3681661).sum := by decide
  have hdescent : baseEnd_3681661 < baseStart_3681661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681668 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_3681668 : Nat := 118140960795 + 3681668 * 2 ^ 59
def prefixEnd_3681668 : Nat := 4983230072969 + 3 ^ 40 * 3681668 * 2
def baseEnd_3681668 : Nat := 1890465294277406690718323

theorem tailTrace_3681668 : CollatzResearch.WordTrace tailWord_3681668 prefixEnd_3681668 1890465294277406690718323 := by
  unfold tailWord_3681668
  simp only [CollatzResearch.WordTrace]
  refine ⟨67140731812976544839934829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89520975750635393119913105 67140731812976544839934829)
  ·
    refine ⟨25177774429866204314975561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67140731812976544839934829 25177774429866204314975561)
    ·
      refine ⟨18883330822399653236231671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25177774429866204314975561 18883330822399653236231671)
      ·
        refine ⟨28324996233599479854347507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18883330822399653236231671 28324996233599479854347507)
        ·
          refine ⟨42487494350399219781521261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28324996233599479854347507 42487494350399219781521261)
          ·
            refine ⟨15932810381399707418070473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42487494350399219781521261 15932810381399707418070473)
            ·
              refine ⟨11949607786049780563552855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15932810381399707418070473 11949607786049780563552855)
              ·
                refine ⟨17924411679074670845329283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11949607786049780563552855 17924411679074670845329283)
                ·
                  refine ⟨26886617518612006267993925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17924411679074670845329283 26886617518612006267993925)
                  ·
                    refine ⟨5041240784739751175248861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26886617518612006267993925 5041240784739751175248861)
                    ·
                      refine ⟨1890465294277406690718323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5041240784739751175248861 1890465294277406690718323)
                      ·
                        rfl

theorem cell23_3681668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_3681668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681668 prefixEnd_3681668 := by exact prefixLift 3681668
  have htrace : WordTrace (prefixWord ++ tailWord_3681668) baseStart_3681668 baseEnd_3681668 := by
    simpa [prefixWord, tailWord_3681668, baseEnd_3681668] using wordTrace_append hprefix tailTrace_3681668
  have hstable : (prefixWord ++ tailWord_3681668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681668).length < 2 ^ (prefixWord ++ tailWord_3681668).sum := by decide
  have hdescent : baseEnd_3681668 < baseStart_3681668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681671 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 8]
def baseStart_3681671 : Nat := 118140960795 + 3681671 * 2 ^ 59
def prefixEnd_3681671 : Nat := 4983230072969 + 3 ^ 40 * 3681671 * 2
def baseEnd_3681671 : Nat := 210051870524374464331201

theorem tailTrace_3681671 : CollatzResearch.WordTrace tailWord_3681671 prefixEnd_3681671 210051870524374464331201 := by
  unfold tailWord_3681671
  simp only [CollatzResearch.WordTrace]
  refine ⟨134281573044942221192228867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89521048696628147461485911 134281573044942221192228867)
  ·
    refine ⟨201422359567413331788343301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134281573044942221192228867 201422359567413331788343301)
    ·
      refine ⟨37766692418889999710314369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201422359567413331788343301 37766692418889999710314369)
      ·
        refine ⟨28325019314167499782735777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37766692418889999710314369 28325019314167499782735777)
        ·
          refine ⟨21243764485625624837051833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28325019314167499782735777 21243764485625624837051833)
          ·
            refine ⟨15932823364219218627788875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21243764485625624837051833 15932823364219218627788875)
            ·
              refine ⟨23899235046328827941683313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15932823364219218627788875 23899235046328827941683313)
              ·
                refine ⟨17924426284746620956262485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23899235046328827941683313 17924426284746620956262485)
                ·
                  refine ⟨210051870524374464331201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17924426284746620956262485 210051870524374464331201)
                  ·
                    rfl

theorem cell23_3681671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 8].length) (baseStart_3681671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681671 prefixEnd_3681671 := by exact prefixLift 3681671
  have htrace : WordTrace (prefixWord ++ tailWord_3681671) baseStart_3681671 baseEnd_3681671 := by
    simpa [prefixWord, tailWord_3681671, baseEnd_3681671] using wordTrace_append hprefix tailTrace_3681671
  have hstable : (prefixWord ++ tailWord_3681671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681671).length < 2 ^ (prefixWord ++ tailWord_3681671).sum := by decide
  have hdescent : baseEnd_3681671 < baseStart_3681671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681681 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 3]
def baseStart_3681681 : Nat := 118140960795 + 3681681 * 2 ^ 59
def prefixEnd_3681681 : Nat := 4983230072969 + 3 ^ 40 * 3681681 * 2
def baseEnd_3681681 : Nat := 1890471969525915139855763

theorem tailTrace_3681681 : CollatzResearch.WordTrace tailWord_3681681 prefixEnd_3681681 1890471969525915139855763 := by
  unfold tailWord_3681681
  simp only [CollatzResearch.WordTrace]
  refine ⟨134281937774905992900092897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89521291849937328600061931 134281937774905992900092897)
  ·
    refine ⟨100711453331179494675069673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134281937774905992900092897 100711453331179494675069673)
    ·
      refine ⟨75533589998384621006302255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100711453331179494675069673 75533589998384621006302255)
      ·
        refine ⟨113300384997576931509453383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75533589998384621006302255 113300384997576931509453383)
        ·
          refine ⟨169950577496365397264180075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113300384997576931509453383 169950577496365397264180075)
          ·
            refine ⟨254925866244548095896270113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169950577496365397264180075 254925866244548095896270113)
            ·
              refine ⟨191194399683411071922202585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254925866244548095896270113 191194399683411071922202585)
              ·
                refine ⟨143395799762558303941651939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191194399683411071922202585 143395799762558303941651939)
                ·
                  refine ⟨215093699643837455912477909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143395799762558303941651939 215093699643837455912477909)
                  ·
                    refine ⟨5041258585402440372948701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 215093699643837455912477909 5041258585402440372948701)
                    ·
                      refine ⟨1890471969525915139855763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5041258585402440372948701 1890471969525915139855763)
                      ·
                        rfl

theorem cell23_3681681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_3681681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681681 prefixEnd_3681681 := by exact prefixLift 3681681
  have htrace : WordTrace (prefixWord ++ tailWord_3681681) baseStart_3681681 baseEnd_3681681 := by
    simpa [prefixWord, tailWord_3681681, baseEnd_3681681] using wordTrace_append hprefix tailTrace_3681681
  have hstable : (prefixWord ++ tailWord_3681681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681681).length < 2 ^ (prefixWord ++ tailWord_3681681).sum := by decide
  have hdescent : baseEnd_3681681 < baseStart_3681681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681682 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3681682 : Nat := 118140960795 + 3681682 * 2 ^ 59
def prefixEnd_3681682 : Nat := 4983230072969 + 3 ^ 40 * 3681682 * 2
def baseEnd_3681682 : Nat := 1890472483006569635943259

theorem tailTrace_3681682 : CollatzResearch.WordTrace tailWord_3681682 prefixEnd_3681682 1890472483006569635943259 := by
  unfold tailWord_3681682
  simp only [CollatzResearch.WordTrace]
  refine ⟨33570493561975592517719825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89521316165268246713919533 33570493561975592517719825)
  ·
    refine ⟨25177870171481694388289869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33570493561975592517719825 25177870171481694388289869)
    ·
      refine ⟨9441701314305635395608701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25177870171481694388289869 9441701314305635395608701)
      ·
        refine ⟨3540637992864613273353263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9441701314305635395608701 3540637992864613273353263)
        ·
          refine ⟨5310956989296919910029895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3540637992864613273353263 5310956989296919910029895)
          ·
            refine ⟨7966435483945379865044843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5310956989296919910029895 7966435483945379865044843)
            ·
              refine ⟨11949653225918069797567265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7966435483945379865044843 11949653225918069797567265)
              ·
                refine ⟨8962239919438552348175449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11949653225918069797567265 8962239919438552348175449)
                ·
                  refine ⟨6721679939578914261131587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8962239919438552348175449 6721679939578914261131587)
                  ·
                    refine ⟨10082519909368371391697381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6721679939578914261131587 10082519909368371391697381)
                    ·
                      refine ⟨1890472483006569635943259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10082519909368371391697381 1890472483006569635943259)
                      ·
                        rfl

theorem cell23_3681682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3681682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681682 prefixEnd_3681682 := by exact prefixLift 3681682
  have htrace : WordTrace (prefixWord ++ tailWord_3681682) baseStart_3681682 baseEnd_3681682 := by
    simpa [prefixWord, tailWord_3681682, baseEnd_3681682] using wordTrace_append hprefix tailTrace_3681682
  have hstable : (prefixWord ++ tailWord_3681682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681682).length < 2 ^ (prefixWord ++ tailWord_3681682).sum := by decide
  have hdescent : baseEnd_3681682 < baseStart_3681682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681708 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 3, 5, 2]
def baseStart_3681708 : Nat := 118140960795 + 3681708 * 2 ^ 59
def prefixEnd_3681708 : Nat := 4983230072969 + 3 ^ 40 * 3681708 * 2
def baseEnd_3681708 : Nat := 1890485833503586534218139

theorem tailTrace_3681708 : CollatzResearch.WordTrace tailWord_3681708 prefixEnd_3681708 1890485833503586534218139 := by
  unfold tailWord_3681708
  simp only [CollatzResearch.WordTrace]
  refine ⟨67141461272904088255662889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89521948363872117674217185 67141461272904088255662889)
  ·
    refine ⟨50356095954678066191747167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67141461272904088255662889 50356095954678066191747167)
    ·
      refine ⟨75534143932017099287620751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50356095954678066191747167 75534143932017099287620751)
      ·
        refine ⟨113301215898025648931431127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75534143932017099287620751 113301215898025648931431127)
        ·
          refine ⟨169951823847038473397146691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113301215898025648931431127 169951823847038473397146691)
          ·
            refine ⟨254927735770557710095720037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169951823847038473397146691 254927735770557710095720037)
            ·
              refine ⟨47798950456979570642947507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254927735770557710095720037 47798950456979570642947507)
              ·
                refine ⟨71698425685469355964421261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47798950456979570642947507 71698425685469355964421261)
                ·
                  refine ⟨26886909632051008486657973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71698425685469355964421261 26886909632051008486657973)
                  ·
                    refine ⟨2520647778004782045624185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26886909632051008486657973 2520647778004782045624185)
                    ·
                      refine ⟨1890485833503586534218139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2520647778004782045624185 1890485833503586534218139)
                      ·
                        rfl

theorem cell23_3681708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 5, 2].length) (baseStart_3681708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681708 prefixEnd_3681708 := by exact prefixLift 3681708
  have htrace : WordTrace (prefixWord ++ tailWord_3681708) baseStart_3681708 baseEnd_3681708 := by
    simpa [prefixWord, tailWord_3681708, baseEnd_3681708] using wordTrace_append hprefix tailTrace_3681708
  have hstable : (prefixWord ++ tailWord_3681708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681708).length < 2 ^ (prefixWord ++ tailWord_3681708).sum := by decide
  have hdescent : baseEnd_3681708 < baseStart_3681708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681731 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 3, 6]
def baseStart_3681731 : Nat := 118140960795 + 3681731 * 2 ^ 59
def prefixEnd_3681731 : Nat := 4983230072969 + 3 ^ 40 * 3681731 * 2
def baseEnd_3681731 : Nat := 630165881186213314743511

theorem tailTrace_3681731 : CollatzResearch.WordTrace tailWord_3681731 prefixEnd_3681731 630165881186213314743511 := by
  unfold tailWord_3681731
  simp only [CollatzResearch.WordTrace]
  refine ⟨134283761424724851439413047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89522507616483234292942031 134283761424724851439413047)
  ·
    refine ⟨201425642137087277159119571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134283761424724851439413047 201425642137087277159119571)
    ·
      refine ⟨302138463205630915738679357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201425642137087277159119571 302138463205630915738679357)
      ·
        refine ⟨113301923702111593402004759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302138463205630915738679357 113301923702111593402004759)
        ·
          refine ⟨169952885553167390103007139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113301923702111593402004759 169952885553167390103007139)
          ·
            refine ⟨254929328329751085154510709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169952885553167390103007139 254929328329751085154510709)
            ·
              refine ⟨23899624530914164233235379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254929328329751085154510709 23899624530914164233235379)
              ·
                refine ⟨35849436796371246349853069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23899624530914164233235379 35849436796371246349853069)
                ·
                  refine ⟨13443538798639217381194901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35849436796371246349853069 13443538798639217381194901)
                  ·
                    refine ⟨630165881186213314743511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13443538798639217381194901 630165881186213314743511)
                    ·
                      rfl

theorem cell23_3681731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 6].length) (baseStart_3681731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681731 prefixEnd_3681731 := by exact prefixLift 3681731
  have htrace : WordTrace (prefixWord ++ tailWord_3681731) baseStart_3681731 baseEnd_3681731 := by
    simpa [prefixWord, tailWord_3681731, baseEnd_3681731] using wordTrace_append hprefix tailTrace_3681731
  have hstable : (prefixWord ++ tailWord_3681731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681731).length < 2 ^ (prefixWord ++ tailWord_3681731).sum := by decide
  have hdescent : baseEnd_3681731 < baseStart_3681731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681735 : List Nat := [1, 1, 4, 1, 1, 3, 5, 1, 1, 5]
def baseStart_3681735 : Nat := 118140960795 + 3681735 * 2 ^ 59
def prefixEnd_3681735 : Nat := 4983230072969 + 3 ^ 40 * 3681735 * 2
def baseEnd_3681735 : Nat := 630166565827085976193505

theorem tailTrace_3681735 : CollatzResearch.WordTrace tailWord_3681735 prefixEnd_3681735 630166565827085976193505 := by
  unfold tailWord_3681735
  simp only [CollatzResearch.WordTrace]
  refine ⟨134283907316710360122558659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89522604877806906748372439 134283907316710360122558659)
  ·
    refine ⟨201425860975065540183837989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134283907316710360122558659 201425860975065540183837989)
    ·
      refine ⟨37767348932824788784469623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201425860975065540183837989 37767348932824788784469623)
      ·
        refine ⟨56651023399237183176704435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37767348932824788784469623 56651023399237183176704435)
        ·
          refine ⟨84976535098855774765056653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56651023399237183176704435 84976535098855774765056653)
          ·
            refine ⟨31866200662070915536896245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84976535098855774765056653 31866200662070915536896245)
            ·
              refine ⟨2987456312069148331584023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31866200662070915536896245 2987456312069148331584023)
              ·
                refine ⟨4481184468103722497376035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987456312069148331584023 4481184468103722497376035)
                ·
                  refine ⟨6721776702155583746064053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4481184468103722497376035 6721776702155583746064053)
                  ·
                    refine ⟨630166565827085976193505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6721776702155583746064053 630166565827085976193505)
                    ·
                      rfl

theorem cell23_3681735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_3681735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681735 prefixEnd_3681735 := by exact prefixLift 3681735
  have htrace : WordTrace (prefixWord ++ tailWord_3681735) baseStart_3681735 baseEnd_3681735 := by
    simpa [prefixWord, tailWord_3681735, baseEnd_3681735] using wordTrace_append hprefix tailTrace_3681735
  have hstable : (prefixWord ++ tailWord_3681735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681735).length < 2 ^ (prefixWord ++ tailWord_3681735).sum := by decide
  have hdescent : baseEnd_3681735 < baseStart_3681735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681751 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_3681751 : Nat := 118140960795 + 3681751 * 2 ^ 59
def prefixEnd_3681751 : Nat := 4983230072969 + 3 ^ 40 * 3681751 * 2
def baseEnd_3681751 : Nat := 1890507913171729865980441

theorem tailTrace_3681751 : CollatzResearch.WordTrace tailWord_3681751 prefixEnd_3681751 1890507913171729865980441 := by
  unfold tailWord_3681751
  simp only [CollatzResearch.WordTrace]
  refine ⟨134284490884652394855141107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89522993923101596570094071 134284490884652394855141107)
  ·
    refine ⟨201426736326978592282711661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134284490884652394855141107 201426736326978592282711661)
    ·
      refine ⟨75535026122616972106016873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201426736326978592282711661 75535026122616972106016873)
      ·
        refine ⟨56651269591962729079512655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75535026122616972106016873 56651269591962729079512655)
        ·
          refine ⟨84976904387944093619268983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56651269591962729079512655 84976904387944093619268983)
          ·
            refine ⟨127465356581916140428903475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84976904387944093619268983 127465356581916140428903475)
            ·
              refine ⟨191198034872874210643355213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127465356581916140428903475 191198034872874210643355213)
              ·
                refine ⟨71699263077327828991258205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191198034872874210643355213 71699263077327828991258205)
                ·
                  refine ⟨26887223653997935871721827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71699263077327828991258205 26887223653997935871721827)
                  ·
                    refine ⟨40330835480996903807582741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26887223653997935871721827 40330835480996903807582741)
                    ·
                      refine ⟨1890507913171729865980441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40330835480996903807582741 1890507913171729865980441)
                      ·
                        rfl

theorem cell23_3681751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_3681751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681751 prefixEnd_3681751 := by exact prefixLift 3681751
  have htrace : WordTrace (prefixWord ++ tailWord_3681751) baseStart_3681751 baseEnd_3681751 := by
    simpa [prefixWord, tailWord_3681751, baseEnd_3681751] using wordTrace_append hprefix tailTrace_3681751
  have hstable : (prefixWord ++ tailWord_3681751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681751).length < 2 ^ (prefixWord ++ tailWord_3681751).sum := by decide
  have hdescent : baseEnd_3681751 < baseStart_3681751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681765 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 1, 6]
def baseStart_3681765 : Nat := 118140960795 + 3681765 * 2 ^ 59
def prefixEnd_3681765 : Nat := 4983230072969 + 3 ^ 40 * 3681765 * 2
def baseEnd_3681765 : Nat := 630171700633630937068459

theorem tailTrace_3681765 : CollatzResearch.WordTrace tailWord_3681765 prefixEnd_3681765 630171700633630937068459 := by
  unfold tailWord_3681765
  simp only [CollatzResearch.WordTrace]
  refine ⟨134285001506601675246150749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89523334337734450164100499 134285001506601675246150749)
  ·
    refine ⟨50356875564975628217306531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134285001506601675246150749 50356875564975628217306531)
    ·
      refine ⟨75535313347463442325959797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50356875564975628217306531 75535313347463442325959797)
      ·
        refine ⟨7081435626324697718058731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75535313347463442325959797 7081435626324697718058731)
        ·
          refine ⟨10622153439487046577088097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7081435626324697718058731 10622153439487046577088097)
          ·
            refine ⟨7966615079615284932816073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10622153439487046577088097 7966615079615284932816073)
            ·
              refine ⟨5974961309711463699612055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7966615079615284932816073 5974961309711463699612055)
              ·
                refine ⟨8962441964567195549418083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5974961309711463699612055 8962441964567195549418083)
                ·
                  refine ⟨13443662946850793324127125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8962441964567195549418083 13443662946850793324127125)
                  ·
                    refine ⟨630171700633630937068459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13443662946850793324127125 630171700633630937068459)
                    ·
                      rfl

theorem cell23_3681765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_3681765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681765 prefixEnd_3681765 := by exact prefixLift 3681765
  have htrace : WordTrace (prefixWord ++ tailWord_3681765) baseStart_3681765 baseEnd_3681765 := by
    simpa [prefixWord, tailWord_3681765, baseEnd_3681765] using wordTrace_append hprefix tailTrace_3681765
  have hstable : (prefixWord ++ tailWord_3681765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681765).length < 2 ^ (prefixWord ++ tailWord_3681765).sum := by decide
  have hdescent : baseEnd_3681765 < baseStart_3681765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681789 : List Nat := [1, 4, 1, 1, 1, 4, 1, 5, 1, 2, 2]
def baseStart_3681789 : Nat := 118140960795 + 3681789 * 2 ^ 59
def prefixEnd_3681789 : Nat := 4983230072969 + 3 ^ 40 * 3681789 * 2
def baseEnd_3681789 : Nat := 1890527425436600717305267

theorem tailTrace_3681789 : CollatzResearch.WordTrace tailWord_3681789 prefixEnd_3681789 1890527425436600717305267 := by
  unfold tailWord_3681789
  simp only [CollatzResearch.WordTrace]
  refine ⟨134285876858514727345024421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89523917905676484896682947 134285876858514727345024421)
  ·
    refine ⟨25178601910971511377192079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134285876858514727345024421 25178601910971511377192079)
    ·
      refine ⟨37767902866457267065788119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25178601910971511377192079 37767902866457267065788119)
      ·
        refine ⟨56651854299685900598682179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37767902866457267065788119 56651854299685900598682179)
        ·
          refine ⟨84977781449528850898023269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56651854299685900598682179 84977781449528850898023269)
          ·
            refine ⟨15933334021786659543379363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84977781449528850898023269 15933334021786659543379363)
            ·
              refine ⟨23900001032679989315069045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15933334021786659543379363 23900001032679989315069045)
              ·
                refine ⟨2240625096813748998287723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23900001032679989315069045 2240625096813748998287723)
                ·
                  refine ⟨3360937645220623497431585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2240625096813748998287723 3360937645220623497431585)
                  ·
                    refine ⟨2520703233915467623073689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3360937645220623497431585 2520703233915467623073689)
                    ·
                      refine ⟨1890527425436600717305267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2520703233915467623073689 1890527425436600717305267)
                      ·
                        rfl

theorem cell23_3681789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_3681789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681789 prefixEnd_3681789 := by exact prefixLift 3681789
  have htrace : WordTrace (prefixWord ++ tailWord_3681789) baseStart_3681789 baseEnd_3681789 := by
    simpa [prefixWord, tailWord_3681789, baseEnd_3681789] using wordTrace_append hprefix tailTrace_3681789
  have hstable : (prefixWord ++ tailWord_3681789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681789).length < 2 ^ (prefixWord ++ tailWord_3681789).sum := by decide
  have hdescent : baseEnd_3681789 < baseStart_3681789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681791 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 1, 9]
def baseStart_3681791 : Nat := 118140960795 + 3681791 * 2 ^ 59
def prefixEnd_3681791 : Nat := 4983230072969 + 3 ^ 40 * 3681791 * 2
def baseEnd_3681791 : Nat := 630176150799303236493419

theorem tailTrace_3681791 : CollatzResearch.WordTrace tailWord_3681791 prefixEnd_3681791 630176150799303236493419 := by
  unfold tailWord_3681791
  simp only [CollatzResearch.WordTrace]
  refine ⟨134285949804507481686597227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89523966536338321124398151 134285949804507481686597227)
  ·
    refine ⟨201428924706761222529895841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134285949804507481686597227 201428924706761222529895841)
    ·
      refine ⟨151071693530070916897421881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201428924706761222529895841 151071693530070916897421881)
      ·
        refine ⟨113303770147553187673066411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151071693530070916897421881 113303770147553187673066411)
        ·
          refine ⟨169955655221329781509599617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113303770147553187673066411 169955655221329781509599617)
          ·
            refine ⟨127466741415997336132199713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169955655221329781509599617 127466741415997336132199713)
            ·
              refine ⟨95600056061998002099149785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127466741415997336132199713 95600056061998002099149785)
              ·
                refine ⟨71700042046498501574362339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95600056061998002099149785 71700042046498501574362339)
                ·
                  refine ⟨107550063069747752361543509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71700042046498501574362339 107550063069747752361543509)
                  ·
                    refine ⟨630176150799303236493419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 107550063069747752361543509 630176150799303236493419)
                    ·
                      rfl

theorem cell23_3681791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 9].length) (baseStart_3681791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681791 prefixEnd_3681791 := by exact prefixLift 3681791
  have htrace : WordTrace (prefixWord ++ tailWord_3681791) baseStart_3681791 baseEnd_3681791 := by
    simpa [prefixWord, tailWord_3681791, baseEnd_3681791] using wordTrace_append hprefix tailTrace_3681791
  have hstable : (prefixWord ++ tailWord_3681791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681791).length < 2 ^ (prefixWord ++ tailWord_3681791).sum := by decide
  have hdescent : baseEnd_3681791 < baseStart_3681791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681848 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 1, 3, 5]
def baseStart_3681848 : Nat := 118140960795 + 3681848 * 2 ^ 59
def prefixEnd_3681848 : Nat := 4983230072969 + 3 ^ 40 * 3681848 * 2
def baseEnd_3681848 : Nat := 1890557720795215986467495

theorem tailTrace_3681848 : CollatzResearch.WordTrace tailWord_3681848 prefixEnd_3681848 1890557720795215986467495 := by
  unfold tailWord_3681848
  simp only [CollatzResearch.WordTrace]
  refine ⟨67144014382650490210711099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89525352510200653614281465 67144014382650490210711099)
  ·
    refine ⟨100716021573975735316066649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67144014382650490210711099 100716021573975735316066649)
    ·
      refine ⟨75537016180481801487049987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100716021573975735316066649 75537016180481801487049987)
      ·
        refine ⟨113305524270722702230574981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75537016180481801487049987 113305524270722702230574981)
        ·
          refine ⟨21244785800760506668232809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113305524270722702230574981 21244785800760506668232809)
          ·
            refine ⟨15933589350570380001174607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21244785800760506668232809 15933589350570380001174607)
            ·
              refine ⟨23900384025855570001761911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15933589350570380001174607 23900384025855570001761911)
              ·
                refine ⟨35850576038783355002642867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23900384025855570001761911 35850576038783355002642867)
                ·
                  refine ⟨53775864058175032503964301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35850576038783355002642867 53775864058175032503964301)
                  ·
                    refine ⟨20165949021815637188986613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53775864058175032503964301 20165949021815637188986613)
                    ·
                      refine ⟨1890557720795215986467495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20165949021815637188986613 1890557720795215986467495)
                      ·
                        rfl

theorem cell23_3681848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_3681848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681848 prefixEnd_3681848 := by exact prefixLift 3681848
  have htrace : WordTrace (prefixWord ++ tailWord_3681848) baseStart_3681848 baseEnd_3681848 := by
    simpa [prefixWord, tailWord_3681848, baseEnd_3681848] using wordTrace_append hprefix tailTrace_3681848
  have hstable : (prefixWord ++ tailWord_3681848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681848).length < 2 ^ (prefixWord ++ tailWord_3681848).sum := by decide
  have hdescent : baseEnd_3681848 < baseStart_3681848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681879 : List Nat := [1, 1, 3, 2, 2, 4, 1, 3, 2, 2, 2]
def baseStart_3681879 : Nat := 118140960795 + 3681879 * 2 ^ 59
def prefixEnd_3681879 : Nat := 4983230072969 + 3 ^ 40 * 3681879 * 2
def baseEnd_3681879 : Nat := 1890573638695505365179853

theorem tailTrace_3681879 : CollatzResearch.WordTrace tailWord_3681879 prefixEnd_3681879 1890573638695505365179853 := by
  unfold tailWord_3681879
  simp only [CollatzResearch.WordTrace]
  refine ⟨134289159428188672715800691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89526106285459115143867127 134289159428188672715800691)
  ·
    refine ⟨201433739142283009073701037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134289159428188672715800691 201433739142283009073701037)
    ·
      refine ⟨75537652178356128402637889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201433739142283009073701037 75537652178356128402637889)
      ·
        refine ⟨56653239133767096301978417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75537652178356128402637889 56653239133767096301978417)
        ·
          refine ⟨42489929350325322226483813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56653239133767096301978417 42489929350325322226483813)
          ·
            refine ⟨7966861753185997917465715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42489929350325322226483813 7966861753185997917465715)
            ·
              refine ⟨11950292629778996876198573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7966861753185997917465715 11950292629778996876198573)
              ·
                refine ⟨4481359736167123828574465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11950292629778996876198573 4481359736167123828574465)
                ·
                  refine ⟨3361019802125342871430849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4481359736167123828574465 3361019802125342871430849)
                  ·
                    refine ⟨2520764851594007153573137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3361019802125342871430849 2520764851594007153573137)
                    ·
                      refine ⟨1890573638695505365179853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2520764851594007153573137 1890573638695505365179853)
                      ·
                        rfl

theorem cell23_3681879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_3681879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681879 prefixEnd_3681879 := by exact prefixLift 3681879
  have htrace : WordTrace (prefixWord ++ tailWord_3681879) baseStart_3681879 baseEnd_3681879 := by
    simpa [prefixWord, tailWord_3681879, baseEnd_3681879] using wordTrace_append hprefix tailTrace_3681879
  have hstable : (prefixWord ++ tailWord_3681879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681879).length < 2 ^ (prefixWord ++ tailWord_3681879).sum := by decide
  have hdescent : baseEnd_3681879 < baseStart_3681879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681905 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 4, 5, 2]
def baseStart_3681905 : Nat := 118140960795 + 3681905 * 2 ^ 59
def prefixEnd_3681905 : Nat := 4983230072969 + 3 ^ 40 * 3681905 * 2
def baseEnd_3681905 : Nat := 1890586989192522263454733

theorem tailTrace_3681905 : CollatzResearch.WordTrace tailWord_3681905 prefixEnd_3681905 1890586989192522263454733 := by
  unfold tailWord_3681905
  simp only [CollatzResearch.WordTrace]
  refine ⟨134290107726094479156247169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89526738484062986104164779 134290107726094479156247169)
  ·
    refine ⟨100717580794570859367185377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134290107726094479156247169 100717580794570859367185377)
    ·
      refine ⟨75538185595928144525389033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100717580794570859367185377 75538185595928144525389033)
      ·
        refine ⟨56653639196946108394041775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75538185595928144525389033 56653639196946108394041775)
        ·
          refine ⟨84980458795419162591062663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56653639196946108394041775 84980458795419162591062663)
          ·
            refine ⟨127470688193128743886593995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84980458795419162591062663 127470688193128743886593995)
            ·
              refine ⟨191206032289693115829890993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127470688193128743886593995 191206032289693115829890993)
              ·
                refine ⟨143404524217269836872418245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191206032289693115829890993 143404524217269836872418245)
                ·
                  refine ⟨26888348290738094413578421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143404524217269836872418245 26888348290738094413578421)
                  ·
                    refine ⟨2520782652256696351272977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26888348290738094413578421 2520782652256696351272977)
                    ·
                      refine ⟨1890586989192522263454733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2520782652256696351272977 1890586989192522263454733)
                      ·
                        rfl

theorem cell23_3681905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_3681905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681905 prefixEnd_3681905 := by exact prefixLift 3681905
  have htrace : WordTrace (prefixWord ++ tailWord_3681905) baseStart_3681905 baseEnd_3681905 := by
    simpa [prefixWord, tailWord_3681905, baseEnd_3681905] using wordTrace_append hprefix tailTrace_3681905
  have hstable : (prefixWord ++ tailWord_3681905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681905).length < 2 ^ (prefixWord ++ tailWord_3681905).sum := by decide
  have hdescent : baseEnd_3681905 < baseStart_3681905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681952 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 4]
def baseStart_3681952 : Nat := 118140960795 + 3681952 * 2 ^ 59
def prefixEnd_3681952 : Nat := 4983230072969 + 3 ^ 40 * 3681952 * 2
def baseEnd_3681952 : Nat := 1890611122783283579567017

theorem tailTrace_3681952 : CollatzResearch.WordTrace tailWord_3681952 prefixEnd_3681952 1890611122783283579567017 := by
  unfold tailWord_3681952
  simp only [CollatzResearch.WordTrace]
  refine ⟨67145910978462103091604055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89527881304616137455472073 67145910978462103091604055)
  ·
    refine ⟨100718866467693154637406083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67145910978462103091604055 100718866467693154637406083)
    ·
      refine ⟨151078299701539731956109125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100718866467693154637406083 151078299701539731956109125)
      ·
        refine ⟨28327181194038699741770461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151078299701539731956109125 28327181194038699741770461)
        ·
          refine ⟨10622692947764512403163923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28327181194038699741770461 10622692947764512403163923)
          ·
            refine ⟨15934039421646768604745885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10622692947764512403163923 15934039421646768604745885)
            ·
              refine ⟨5975264783117538226779707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15934039421646768604745885 5975264783117538226779707)
              ·
                refine ⟨8962897174676307340169561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5975264783117538226779707 8962897174676307340169561)
                ·
                  refine ⟨6722172881007230505127171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8962897174676307340169561 6722172881007230505127171)
                  ·
                    refine ⟨10083259321510845757690757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6722172881007230505127171 10083259321510845757690757)
                    ·
                      refine ⟨1890611122783283579567017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10083259321510845757690757 1890611122783283579567017)
                      ·
                        rfl

theorem cell23_3681952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_3681952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681952 prefixEnd_3681952 := by exact prefixLift 3681952
  have htrace : WordTrace (prefixWord ++ tailWord_3681952) baseStart_3681952 baseEnd_3681952 := by
    simpa [prefixWord, tailWord_3681952, baseEnd_3681952] using wordTrace_append hprefix tailTrace_3681952
  have hstable : (prefixWord ++ tailWord_3681952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681952).length < 2 ^ (prefixWord ++ tailWord_3681952).sum := by decide
  have hdescent : baseEnd_3681952 < baseStart_3681952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681955 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 3]
def baseStart_3681955 : Nat := 118140960795 + 3681955 * 2 ^ 59
def prefixEnd_3681955 : Nat := 4983230072969 + 3 ^ 40 * 3681955 * 2
def baseEnd_3681955 : Nat := 1890612663225247067829503

theorem tailTrace_3681955 : CollatzResearch.WordTrace tailWord_3681955 prefixEnd_3681955 1890612663225247067829503 := by
  unfold tailWord_3681955
  simp only [CollatzResearch.WordTrace]
  refine ⟨134291931375913337695567319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89527954250608891797044879 134291931375913337695567319)
  ·
    refine ⟨201437897063870006543350979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134291931375913337695567319 201437897063870006543350979)
    ·
      refine ⟨302156845595805009815026469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201437897063870006543350979 302156845595805009815026469)
      ·
        refine ⟨56654408549213439340317463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302156845595805009815026469 56654408549213439340317463)
        ·
          refine ⟨84981612823820159010476195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56654408549213439340317463 84981612823820159010476195)
          ·
            refine ⟨127472419235730238515714293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84981612823820159010476195 127472419235730238515714293)
            ·
              refine ⟨11950539303349709860848215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127472419235730238515714293 11950539303349709860848215)
              ·
                refine ⟨17925808955024564791272323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11950539303349709860848215 17925808955024564791272323)
                ·
                  refine ⟨26888713432536847186908485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17925808955024564791272323 26888713432536847186908485)
                  ·
                    refine ⟨5041633768600658847545341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26888713432536847186908485 5041633768600658847545341)
                    ·
                      refine ⟨1890612663225247067829503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5041633768600658847545341 1890612663225247067829503)
                      ·
                        rfl

theorem cell23_3681955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_3681955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681955 prefixEnd_3681955 := by exact prefixLift 3681955
  have htrace : WordTrace (prefixWord ++ tailWord_3681955) baseStart_3681955 baseEnd_3681955 := by
    simpa [prefixWord, tailWord_3681955, baseEnd_3681955] using wordTrace_append hprefix tailTrace_3681955
  have hstable : (prefixWord ++ tailWord_3681955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681955).length < 2 ^ (prefixWord ++ tailWord_3681955).sum := by decide
  have hdescent : baseEnd_3681955 < baseStart_3681955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681965 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_3681965 : Nat := 118140960795 + 3681965 * 2 ^ 59
def prefixEnd_3681965 : Nat := 4983230072969 + 3 ^ 40 * 3681965 * 2
def baseEnd_3681965 : Nat := 1890617798031792028704457

theorem tailTrace_3681965 : CollatzResearch.WordTrace tailWord_3681965 prefixEnd_3681965 1890617798031792028704457 := by
  unfold tailWord_3681965
  simp only [CollatzResearch.WordTrace]
  refine ⟨134292296105877109403431349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89528197403918072935620899 134292296105877109403431349)
  ·
    refine ⟨12589902759925979006571689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134292296105877109403431349 12589902759925979006571689)
    ·
      refine ⟨9442427069944484254928767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12589902759925979006571689 9442427069944484254928767)
      ·
        refine ⟨14163640604916726382393151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9442427069944484254928767 14163640604916726382393151)
        ·
          refine ⟨21245460907375089573589727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14163640604916726382393151 21245460907375089573589727)
          ·
            refine ⟨31868191361062634360384591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21245460907375089573589727 31868191361062634360384591)
            ·
              refine ⟨47802287041593951540576887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31868191361062634360384591 47802287041593951540576887)
              ·
                refine ⟨71703430562390927310865331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47802287041593951540576887 71703430562390927310865331)
                ·
                  refine ⟨107555145843586390966297997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71703430562390927310865331 107555145843586390966297997)
                  ·
                    refine ⟨40333179691344896612361749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107555145843586390966297997 40333179691344896612361749)
                    ·
                      refine ⟨1890617798031792028704457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40333179691344896612361749 1890617798031792028704457)
                      ·
                        rfl

theorem cell23_3681965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_3681965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681965 prefixEnd_3681965 := by exact prefixLift 3681965
  have htrace : WordTrace (prefixWord ++ tailWord_3681965) baseStart_3681965 baseEnd_3681965 := by
    simpa [prefixWord, tailWord_3681965, baseEnd_3681965] using wordTrace_append hprefix tailTrace_3681965
  have hstable : (prefixWord ++ tailWord_3681965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681965).length < 2 ^ (prefixWord ++ tailWord_3681965).sum := by decide
  have hdescent : baseEnd_3681965 < baseStart_3681965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681975 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 8]
def baseStart_3681975 : Nat := 118140960795 + 3681975 * 2 ^ 59
def prefixEnd_3681975 : Nat := 4983230072969 + 3 ^ 40 * 3681975 * 2
def baseEnd_3681975 : Nat := 210069214759815221064379

theorem tailTrace_3681975 : CollatzResearch.WordTrace tailWord_3681975 prefixEnd_3681975 210069214759815221064379 := by
  unfold tailWord_3681975
  simp only [CollatzResearch.WordTrace]
  refine ⟨134292660835840881111295379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89528440557227254074196919 134292660835840881111295379)
  ·
    refine ⟨201438991253761321666943069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134292660835840881111295379 201438991253761321666943069)
    ·
      refine ⟨75539621720160495625103651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201438991253761321666943069 75539621720160495625103651)
      ·
        refine ⟨113309432580240743437655477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75539621720160495625103651 113309432580240743437655477)
        ·
          refine ⟨10622759304397569697280201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113309432580240743437655477 10622759304397569697280201)
          ·
            refine ⟨7967069478298177272960151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10622759304397569697280201 7967069478298177272960151)
            ·
              refine ⟨11950604217447265909440227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7967069478298177272960151 11950604217447265909440227)
              ·
                refine ⟨17925906326170898864160341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11950604217447265909440227 17925906326170898864160341)
                ·
                  refine ⟨210069214759815221064379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17925906326170898864160341 210069214759815221064379)
                  ·
                    rfl

theorem cell23_3681975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 8].length) (baseStart_3681975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681975 prefixEnd_3681975 := by exact prefixLift 3681975
  have htrace : WordTrace (prefixWord ++ tailWord_3681975) baseStart_3681975 baseEnd_3681975 := by
    simpa [prefixWord, tailWord_3681975, baseEnd_3681975] using wordTrace_append hprefix tailTrace_3681975
  have hstable : (prefixWord ++ tailWord_3681975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681975).length < 2 ^ (prefixWord ++ tailWord_3681975).sum := by decide
  have hdescent : baseEnd_3681975 < baseStart_3681975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3681992 : List Nat := [2, 1, 3, 1, 2, 2, 5, 1, 6]
def baseStart_3681992 : Nat := 118140960795 + 3681992 * 2 ^ 59
def prefixEnd_3681992 : Nat := 4983230072969 + 3 ^ 40 * 3681992 * 2
def baseEnd_3681992 : Nat := 210070184667718158118537

theorem tailTrace_3681992 : CollatzResearch.WordTrace tailWord_3681992 prefixEnd_3681992 210070184667718158118537 := by
  unfold tailWord_3681992
  simp only [CollatzResearch.WordTrace]
  refine ⟨67146640438389646507332115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89528853917852862009776153 67146640438389646507332115)
  ·
    refine ⟨100719960657584469760998173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67146640438389646507332115 100719960657584469760998173)
    ·
      refine ⟨37769985246594176160374315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100719960657584469760998173 37769985246594176160374315)
      ·
        refine ⟨56654977869891264240561473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37769985246594176160374315 56654977869891264240561473)
        ·
          refine ⟨42491233402418448180421105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56654977869891264240561473 42491233402418448180421105)
          ·
            refine ⟨31868425051813836135315829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42491233402418448180421105 31868425051813836135315829)
            ·
              refine ⟨2987664848607547137685859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31868425051813836135315829 2987664848607547137685859)
              ·
                refine ⟨4481497272911320706528789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2987664848607547137685859 4481497272911320706528789)
                ·
                  refine ⟨210070184667718158118537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4481497272911320706528789 210070184667718158118537)
                  ·
                    rfl

theorem cell23_3681992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 1, 6].length) (baseStart_3681992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3681992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3681992 prefixEnd_3681992 := by exact prefixLift 3681992
  have htrace : WordTrace (prefixWord ++ tailWord_3681992) baseStart_3681992 baseEnd_3681992 := by
    simpa [prefixWord, tailWord_3681992, baseEnd_3681992] using wordTrace_append hprefix tailTrace_3681992
  have hstable : (prefixWord ++ tailWord_3681992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3681992).length < 2 ^ (prefixWord ++ tailWord_3681992).sum := by decide
  have hdescent : baseEnd_3681992 < baseStart_3681992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3681992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682025 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 5, 1, 4]
def baseStart_3682025 : Nat := 118140960795 + 3682025 * 2 ^ 59
def prefixEnd_3682025 : Nat := 4983230072969 + 3 ^ 40 * 3682025 * 2
def baseEnd_3682025 : Nat := 1890648606871061793954181

theorem tailTrace_3682025 : CollatzResearch.WordTrace tailWord_3682025 prefixEnd_3682025 1890648606871061793954181 := by
  unfold tailWord_3682025
  simp only [CollatzResearch.WordTrace]
  refine ⟨134294484485659739650615529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89529656323773159767077019 134294484485659739650615529)
  ·
    refine ⟨100720863364244804737961647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134294484485659739650615529 100720863364244804737961647)
    ·
      refine ⟨151081295046367207106942471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100720863364244804737961647 151081295046367207106942471)
      ·
        refine ⟨226621942569550810660413707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151081295046367207106942471 226621942569550810660413707)
        ·
          refine ⟨339932913854326215990620561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226621942569550810660413707 339932913854326215990620561)
          ·
            refine ⟨254949685390744661992965421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339932913854326215990620561 254949685390744661992965421)
            ·
              refine ⟨95606132021529248247362033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254949685390744661992965421 95606132021529248247362033)
              ·
                refine ⟨71704599016146936185521525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95606132021529248247362033 71704599016146936185521525)
                ·
                  refine ⟨6722306157763775267392643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71704599016146936185521525 6722306157763775267392643)
                  ·
                    refine ⟨10083459236645662901088965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6722306157763775267392643 10083459236645662901088965)
                    ·
                      refine ⟨1890648606871061793954181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10083459236645662901088965 1890648606871061793954181)
                      ·
                        rfl

theorem cell23_3682025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_3682025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682025 prefixEnd_3682025 := by exact prefixLift 3682025
  have htrace : WordTrace (prefixWord ++ tailWord_3682025) baseStart_3682025 baseEnd_3682025 := by
    simpa [prefixWord, tailWord_3682025, baseEnd_3682025] using wordTrace_append hprefix tailTrace_3682025
  have hstable : (prefixWord ++ tailWord_3682025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682025).length < 2 ^ (prefixWord ++ tailWord_3682025).sum := by decide
  have hdescent : baseEnd_3682025 < baseStart_3682025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682029 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 4, 3, 2]
def baseStart_3682029 : Nat := 118140960795 + 3682029 * 2 ^ 59
def prefixEnd_3682029 : Nat := 4983230072969 + 3 ^ 40 * 3682029 * 2
def baseEnd_3682029 : Nat := 1890650660793679778304163

theorem tailTrace_3682029 : CollatzResearch.WordTrace tailWord_3682029 prefixEnd_3682029 1890650660793679778304163 := by
  unfold tailWord_3682029
  simp only [CollatzResearch.WordTrace]
  refine ⟨134294630377645248333761141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89529753585096832222507427 134294630377645248333761141)
  ·
    refine ⟨12590121597904242031290107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134294630377645248333761141 12590121597904242031290107)
    ·
      refine ⟨18885182396856363046935161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12590121597904242031290107 18885182396856363046935161)
      ·
        refine ⟨14163886797642272285201371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18885182396856363046935161 14163886797642272285201371)
        ·
          refine ⟨21245830196463408427802057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14163886797642272285201371 21245830196463408427802057)
          ·
            refine ⟨15934372647347556320851543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21245830196463408427802057 15934372647347556320851543)
            ·
              refine ⟨23901558971021334481277315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15934372647347556320851543 23901558971021334481277315)
              ·
                refine ⟨35852338456532001721915973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23901558971021334481277315 35852338456532001721915973)
                ·
                  refine ⟨6722313460599750322859245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35852338456532001721915973 6722313460599750322859245)
                  ·
                    refine ⟨2520867547724906371072217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6722313460599750322859245 2520867547724906371072217)
                    ·
                      refine ⟨1890650660793679778304163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2520867547724906371072217 1890650660793679778304163)
                      ·
                        rfl

theorem cell23_3682029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_3682029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682029 prefixEnd_3682029 := by exact prefixLift 3682029
  have htrace : WordTrace (prefixWord ++ tailWord_3682029) baseStart_3682029 baseEnd_3682029 := by
    simpa [prefixWord, tailWord_3682029, baseEnd_3682029] using wordTrace_append hprefix tailTrace_3682029
  have hstable : (prefixWord ++ tailWord_3682029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682029).length < 2 ^ (prefixWord ++ tailWord_3682029).sum := by decide
  have hdescent : baseEnd_3682029 < baseStart_3682029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682045 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_3682045 : Nat := 118140960795 + 3682045 * 2 ^ 59
def prefixEnd_3682045 : Nat := 4983230072969 + 3 ^ 40 * 3682045 * 2
def baseEnd_3682045 : Nat := 1890658876484151715704089

theorem tailTrace_3682045 : CollatzResearch.WordTrace tailWord_3682045 prefixEnd_3682045 1890658876484151715704089 := by
  unfold tailWord_3682045
  simp only [CollatzResearch.WordTrace]
  refine ⟨134295213945587283066343589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89530142630391522044229059 134295213945587283066343589)
  ·
    refine ⟨25180352614797615574939423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134295213945587283066343589 25180352614797615574939423)
    ·
      refine ⟨37770528922196423362409135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25180352614797615574939423 37770528922196423362409135)
      ·
        refine ⟨56655793383294635043613703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37770528922196423362409135 56655793383294635043613703)
        ·
          refine ⟨84983690074941952565420555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56655793383294635043613703 84983690074941952565420555)
          ·
            refine ⟨127475535112412928848130833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84983690074941952565420555 127475535112412928848130833)
            ·
              refine ⟨95606651334309696636098125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127475535112412928848130833 95606651334309696636098125)
              ·
                refine ⟨35852494250366136238536797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95606651334309696636098125 35852494250366136238536797)
                ·
                  refine ⟨13444685343887301089451299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35852494250366136238536797 13444685343887301089451299)
                  ·
                    refine ⟨20167028015830951634176949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13444685343887301089451299 20167028015830951634176949)
                    ·
                      refine ⟨1890658876484151715704089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20167028015830951634176949 1890658876484151715704089)
                      ·
                        rfl

theorem cell23_3682045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_3682045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682045 prefixEnd_3682045 := by exact prefixLift 3682045
  have htrace : WordTrace (prefixWord ++ tailWord_3682045) baseStart_3682045 baseEnd_3682045 := by
    simpa [prefixWord, tailWord_3682045, baseEnd_3682045] using wordTrace_append hprefix tailTrace_3682045
  have hstable : (prefixWord ++ tailWord_3682045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682045).length < 2 ^ (prefixWord ++ tailWord_3682045).sum := by decide
  have hdescent : baseEnd_3682045 < baseStart_3682045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682059 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 3, 2, 2]
def baseStart_3682059 : Nat := 118140960795 + 3682059 * 2 ^ 59
def prefixEnd_3682059 : Nat := 4983230072969 + 3 ^ 40 * 3682059 * 2
def baseEnd_3682059 : Nat := 1890666065213314660929025

theorem tailTrace_3682059 : CollatzResearch.WordTrace tailWord_3682059 prefixEnd_3682059 1890666065213314660929025 := by
  unfold tailWord_3682059
  simp only [CollatzResearch.WordTrace]
  refine ⟨134295724567536563457353231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89530483045024375638235487 134295724567536563457353231)
  ·
    refine ⟨201443586851304845186029847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134295724567536563457353231 201443586851304845186029847)
    ·
      refine ⟨302165380276957267779044771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201443586851304845186029847 302165380276957267779044771)
      ·
        refine ⟨453248070415435901668567157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302165380276957267779044771 453248070415435901668567157)
        ·
          refine ⟨42492006601447115781428171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 453248070415435901668567157 42492006601447115781428171)
          ·
            refine ⟨63738009902170673672142257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42492006601447115781428171 63738009902170673672142257)
            ·
              refine ⟨47803507426628005254106693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63738009902170673672142257 47803507426628005254106693)
              ·
                refine ⟨8963157642492750985145005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47803507426628005254106693 8963157642492750985145005)
                ·
                  refine ⟨3361184115934781619429377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8963157642492750985145005 3361184115934781619429377)
                  ·
                    refine ⟨2520888086951086214572033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3361184115934781619429377 2520888086951086214572033)
                    ·
                      refine ⟨1890666065213314660929025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2520888086951086214572033 1890666065213314660929025)
                      ·
                        rfl

theorem cell23_3682059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 3, 2, 2].length) (baseStart_3682059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682059 prefixEnd_3682059 := by exact prefixLift 3682059
  have htrace : WordTrace (prefixWord ++ tailWord_3682059) baseStart_3682059 baseEnd_3682059 := by
    simpa [prefixWord, tailWord_3682059, baseEnd_3682059] using wordTrace_append hprefix tailTrace_3682059
  have hstable : (prefixWord ++ tailWord_3682059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682059).length < 2 ^ (prefixWord ++ tailWord_3682059).sum := by decide
  have hdescent : baseEnd_3682059 < baseStart_3682059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682099 : List Nat := [1, 1, 1, 2, 8, 1, 1, 8]
def baseStart_3682099 : Nat := 118140960795 + 3682099 * 2 ^ 59
def prefixEnd_3682099 : Nat := 4983230072969 + 3 ^ 40 * 3682099 * 2
def baseEnd_3682099 : Nat := 70025429794055352015883

theorem tailTrace_3682099 : CollatzResearch.WordTrace tailWord_3682099 prefixEnd_3682099 70025429794055352015883 := by
  unfold tailWord_3682099
  simp only [CollatzResearch.WordTrace]
  refine ⟨134297183487391650288809351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89531455658261100192539567 134297183487391650288809351)
  ·
    refine ⟨201445775231087475433214027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134297183487391650288809351 201445775231087475433214027)
    ·
      refine ⟨302168662846631213149821041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201445775231087475433214027 302168662846631213149821041)
      ·
        refine ⟨226626497134973409862365781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302168662846631213149821041 226626497134973409862365781)
        ·
          refine ⟨2655779263300469646824599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 226626497134973409862365781 2655779263300469646824599)
          ·
            refine ⟨3983668894950704470236899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655779263300469646824599 3983668894950704470236899)
            ·
              refine ⟨5975503342426056705355349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3983668894950704470236899 5975503342426056705355349)
              ·
                refine ⟨70025429794055352015883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5975503342426056705355349 70025429794055352015883)
                ·
                  rfl

theorem cell23_3682099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 8].length) (baseStart_3682099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682099 prefixEnd_3682099 := by exact prefixLift 3682099
  have htrace : WordTrace (prefixWord ++ tailWord_3682099) baseStart_3682099 baseEnd_3682099 := by
    simpa [prefixWord, tailWord_3682099, baseEnd_3682099] using wordTrace_append hprefix tailTrace_3682099
  have hstable : (prefixWord ++ tailWord_3682099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682099).length < 2 ^ (prefixWord ++ tailWord_3682099).sum := by decide
  have hdescent : baseEnd_3682099 < baseStart_3682099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682109 : List Nat := [1, 4, 1, 4, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3682109 : Nat := 118140960795 + 3682109 * 2 ^ 59
def prefixEnd_3682109 : Nat := 4983230072969 + 3 ^ 40 * 3682109 * 2
def baseEnd_3682109 : Nat := 1890691739246039465303795

theorem tailTrace_3682109 : CollatzResearch.WordTrace tailWord_3682109 prefixEnd_3682109 1890691739246039465303795 := by
  unfold tailWord_3682109
  simp only [CollatzResearch.WordTrace]
  refine ⟨134297548217355421996673381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89531698811570281331115587 134297548217355421996673381)
  ·
    refine ⟨25180790290754141624376259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134297548217355421996673381 25180790290754141624376259)
    ·
      refine ⟨37771185436131212436564389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25180790290754141624376259 37771185436131212436564389)
      ·
        refine ⟨7082097269274602331855823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37771185436131212436564389 7082097269274602331855823)
        ·
          refine ⟨10623145903911903497783735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7082097269274602331855823 10623145903911903497783735)
          ·
            refine ⟨15934718855867855246675603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10623145903911903497783735 15934718855867855246675603)
            ·
              refine ⟨23902078283801782870013405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15934718855867855246675603 23902078283801782870013405)
              ·
                refine ⟨8963279356425668576255027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23902078283801782870013405 8963279356425668576255027)
                ·
                  refine ⟨13444919034638502864382541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8963279356425668576255027 13444919034638502864382541)
                  ·
                    refine ⟨5041844637989438574143453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13444919034638502864382541 5041844637989438574143453)
                    ·
                      refine ⟨1890691739246039465303795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5041844637989438574143453 1890691739246039465303795)
                      ·
                        rfl

theorem cell23_3682109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3682109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682109 prefixEnd_3682109 := by exact prefixLift 3682109
  have htrace : WordTrace (prefixWord ++ tailWord_3682109) baseStart_3682109 baseEnd_3682109 := by
    simpa [prefixWord, tailWord_3682109, baseEnd_3682109] using wordTrace_append hprefix tailTrace_3682109
  have hstable : (prefixWord ++ tailWord_3682109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682109).length < 2 ^ (prefixWord ++ tailWord_3682109).sum := by decide
  have hdescent : baseEnd_3682109 < baseStart_3682109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682119 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 3, 3, 2]
def baseStart_3682119 : Nat := 118140960795 + 3682119 * 2 ^ 59
def prefixEnd_3682119 : Nat := 4983230072969 + 3 ^ 40 * 3682119 * 2
def baseEnd_3682119 : Nat := 1890696874052584426178749

theorem tailTrace_3682119 : CollatzResearch.WordTrace tailWord_3682119 prefixEnd_3682119 1890696874052584426178749 := by
  unfold tailWord_3682119
  simp only [CollatzResearch.WordTrace]
  refine ⟨134297912947319193704537411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89531941964879462469691607 134297912947319193704537411)
  ·
    refine ⟨201446869420978790556806117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134297912947319193704537411 201446869420978790556806117)
    ·
      refine ⟨37771288016433523229401147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201446869420978790556806117 37771288016433523229401147)
      ·
        refine ⟨56656932024650284844101721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37771288016433523229401147 56656932024650284844101721)
        ·
          refine ⟨42492699018487713633076291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56656932024650284844101721 42492699018487713633076291)
          ·
            refine ⟨63739048527731570449614437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42492699018487713633076291 63739048527731570449614437)
            ·
              refine ⟨11951071598949669459302707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63739048527731570449614437 11951071598949669459302707)
              ·
                refine ⟨17926607398424504188954061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11951071598949669459302707 17926607398424504188954061)
                ·
                  refine ⟨6722477774409189070857773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17926607398424504188954061 6722477774409189070857773)
                  ·
                    refine ⟨2520929165403445901571665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6722477774409189070857773 2520929165403445901571665)
                    ·
                      refine ⟨1890696874052584426178749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2520929165403445901571665 1890696874052584426178749)
                      ·
                        rfl

theorem cell23_3682119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_3682119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682119 prefixEnd_3682119 := by exact prefixLift 3682119
  have htrace : WordTrace (prefixWord ++ tailWord_3682119) baseStart_3682119 baseEnd_3682119 := by
    simpa [prefixWord, tailWord_3682119, baseEnd_3682119] using wordTrace_append hprefix tailTrace_3682119
  have hstable : (prefixWord ++ tailWord_3682119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682119).length < 2 ^ (prefixWord ++ tailWord_3682119).sum := by decide
  have hdescent : baseEnd_3682119 < baseStart_3682119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682212 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_3682212 : Nat := 118140960795 + 3682212 * 2 ^ 59
def prefixEnd_3682212 : Nat := 4983230072969 + 3 ^ 40 * 3682212 * 2
def baseEnd_3682212 : Nat := 1890744627753452562315821

theorem tailTrace_3682212 : CollatzResearch.WordTrace tailWord_3682212 prefixEnd_3682212 1890744627753452562315821 := by
  unfold tailWord_3682212
  simp only [CollatzResearch.WordTrace]
  refine ⟨67150652467991135293836445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89534203290654847058448593 67150652467991135293836445)
  ·
    refine ⟨25181494675496675735188667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67150652467991135293836445 25181494675496675735188667)
    ·
      refine ⟨37772242013245013602783001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25181494675496675735188667 37772242013245013602783001)
      ·
        refine ⟨28329181509933760202087251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37772242013245013602783001 28329181509933760202087251)
        ·
          refine ⟨42493772264900640303130877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28329181509933760202087251 42493772264900640303130877)
          ·
            refine ⟨15935164599337740113674079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42493772264900640303130877 15935164599337740113674079)
            ·
              refine ⟨23902746899006610170511119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15935164599337740113674079 23902746899006610170511119)
              ·
                refine ⟨35854120348509915255766679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23902746899006610170511119 35854120348509915255766679)
                ·
                  refine ⟨53781180522764872883650019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35854120348509915255766679 53781180522764872883650019)
                  ·
                    refine ⟨80671770784147309325475029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53781180522764872883650019 80671770784147309325475029)
                    ·
                      refine ⟨1890744627753452562315821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80671770784147309325475029 1890744627753452562315821)
                      ·
                        rfl

theorem cell23_3682212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_3682212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682212 prefixEnd_3682212 := by exact prefixLift 3682212
  have htrace : WordTrace (prefixWord ++ tailWord_3682212) baseStart_3682212 baseEnd_3682212 := by
    simpa [prefixWord, tailWord_3682212, baseEnd_3682212] using wordTrace_append hprefix tailTrace_3682212
  have hstable : (prefixWord ++ tailWord_3682212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682212).length < 2 ^ (prefixWord ++ tailWord_3682212).sum := by decide
  have hdescent : baseEnd_3682212 < baseStart_3682212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682239 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 4]
def baseStart_3682239 : Nat := 118140960795 + 3682239 * 2 ^ 59
def prefixEnd_3682239 : Nat := 4983230072969 + 3 ^ 40 * 3682239 * 2
def baseEnd_3682239 : Nat := 1890758491731123956678197

theorem tailTrace_3682239 : CollatzResearch.WordTrace tailWord_3682239 prefixEnd_3682239 1890758491731123956678197 := by
  unfold tailWord_3682239
  simp only [CollatzResearch.WordTrace]
  refine ⟨134302289706884454198905771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89534859804589636132603847 134302289706884454198905771)
  ·
    refine ⟨201453434560326681298358657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134302289706884454198905771 201453434560326681298358657)
    ·
      refine ⟨151090075920245010973768993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201453434560326681298358657 151090075920245010973768993)
      ·
        refine ⟨113317556940183758230326745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151090075920245010973768993 113317556940183758230326745)
        ·
          refine ⟨84988167705137818672745059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113317556940183758230326745 84988167705137818672745059)
          ·
            refine ⟨127482251557706728009117589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84988167705137818672745059 127482251557706728009117589)
            ·
              refine ⟨5975730541767502875427387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127482251557706728009117589 5975730541767502875427387)
              ·
                refine ⟨8963595812651254313141081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5975730541767502875427387 8963595812651254313141081)
                ·
                  refine ⟨6722696859488440734855811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8963595812651254313141081 6722696859488440734855811)
                  ·
                    refine ⟨10084045289232661102283717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6722696859488440734855811 10084045289232661102283717)
                    ·
                      refine ⟨1890758491731123956678197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10084045289232661102283717 1890758491731123956678197)
                      ·
                        rfl

theorem cell23_3682239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_3682239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682239 prefixEnd_3682239 := by exact prefixLift 3682239
  have htrace : WordTrace (prefixWord ++ tailWord_3682239) baseStart_3682239 baseEnd_3682239 := by
    simpa [prefixWord, tailWord_3682239, baseEnd_3682239] using wordTrace_append hprefix tailTrace_3682239
  have hstable : (prefixWord ++ tailWord_3682239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682239).length < 2 ^ (prefixWord ++ tailWord_3682239).sum := by decide
  have hdescent : baseEnd_3682239 < baseStart_3682239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682316 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 4, 3, 2]
def baseStart_3682316 : Nat := 118140960795 + 3682316 * 2 ^ 59
def prefixEnd_3682316 : Nat := 4983230072969 + 3 ^ 40 * 3682316 * 2
def baseEnd_3682316 : Nat := 1890798029741520155415343

theorem tailTrace_3682316 : CollatzResearch.WordTrace tailWord_3682316 prefixEnd_3682316 1890798029741520155415343 := by
  unfold tailWord_3682316
  simp only [CollatzResearch.WordTrace]
  refine ⟨67152549063802748174729401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89536732085070330899639201 67152549063802748174729401)
  ·
    refine ⟨50364411797852061131047051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67152549063802748174729401 50364411797852061131047051)
    ·
      refine ⟨75546617696778091696570577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50364411797852061131047051 75546617696778091696570577)
      ·
        refine ⟨56659963272583568772427933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75546617696778091696570577 56659963272583568772427933)
        ·
          refine ⟨21247486227218838289660475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56659963272583568772427933 21247486227218838289660475)
          ·
            refine ⟨31871229340828257434490713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21247486227218838289660475 31871229340828257434490713)
            ·
              refine ⟨23903422005621193075868035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31871229340828257434490713 23903422005621193075868035)
              ·
                refine ⟨35855133008431789613802053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23903422005621193075868035 35855133008431789613802053)
                ·
                  refine ⟨6722837439080960552587885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35855133008431789613802053 6722837439080960552587885)
                  ·
                    refine ⟨2521064039655360207220457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6722837439080960552587885 2521064039655360207220457)
                    ·
                      refine ⟨1890798029741520155415343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2521064039655360207220457 1890798029741520155415343)
                      ·
                        rfl

theorem cell23_3682316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_3682316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682316 prefixEnd_3682316 := by exact prefixLift 3682316
  have htrace : WordTrace (prefixWord ++ tailWord_3682316) baseStart_3682316 baseEnd_3682316 := by
    simpa [prefixWord, tailWord_3682316, baseEnd_3682316] using wordTrace_append hprefix tailTrace_3682316
  have hstable : (prefixWord ++ tailWord_3682316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682316).length < 2 ^ (prefixWord ++ tailWord_3682316).sum := by decide
  have hdescent : baseEnd_3682316 < baseStart_3682316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682317 : List Nat := [1, 7, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3682317 : Nat := 118140960795 + 3682317 * 2 ^ 59
def prefixEnd_3682317 : Nat := 4983230072969 + 3 ^ 40 * 3682317 * 2
def baseEnd_3682317 : Nat := 630266181074058217167613

theorem tailTrace_3682317 : CollatzResearch.WordTrace tailWord_3682317 prefixEnd_3682317 630266181074058217167613 := by
  unfold tailWord_3682317
  simp only [CollatzResearch.WordTrace]
  refine ⟨134305134600601873520245205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89536756400401249013496803 134305134600601873520245205)
  ·
    refine ⟨3147776592201606410630747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 134305134600601873520245205 3147776592201606410630747)
    ·
      refine ⟨4721664888302409615946121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3147776592201606410630747 4721664888302409615946121)
      ·
        refine ⟨3541248666226807211959591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4721664888302409615946121 3541248666226807211959591)
        ·
          refine ⟨5311872999340210817939387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3541248666226807211959591 5311872999340210817939387)
          ·
            refine ⟨7967809499010316226909081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5311872999340210817939387 7967809499010316226909081)
            ·
              refine ⟨5975857124257737170181811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7967809499010316226909081 5975857124257737170181811)
              ·
                refine ⟨8963785686386605755272717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5975857124257737170181811 8963785686386605755272717)
                ·
                  refine ⟨3361419632394977158227269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8963785686386605755272717 3361419632394977158227269)
                  ·
                    refine ⟨630266181074058217167613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3361419632394977158227269 630266181074058217167613)
                    ·
                      rfl

theorem cell23_3682317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3682317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682317 prefixEnd_3682317 := by exact prefixLift 3682317
  have htrace : WordTrace (prefixWord ++ tailWord_3682317) baseStart_3682317 baseEnd_3682317 := by
    simpa [prefixWord, tailWord_3682317, baseEnd_3682317] using wordTrace_append hprefix tailTrace_3682317
  have hstable : (prefixWord ++ tailWord_3682317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682317).length < 2 ^ (prefixWord ++ tailWord_3682317).sum := by decide
  have hdescent : baseEnd_3682317 < baseStart_3682317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682323 : List Nat := [1, 1, 1, 2, 1, 4, 4, 4, 1, 1, 3]
def baseStart_3682323 : Nat := 118140960795 + 3682323 * 2 ^ 59
def prefixEnd_3682323 : Nat := 4983230072969 + 3 ^ 40 * 3682323 * 2
def baseEnd_3682323 : Nat := 1890801624106101628027811

theorem tailTrace_3682323 : CollatzResearch.WordTrace tailWord_3682323 prefixEnd_3682323 1890801624106101628027811 := by
  unfold tailWord_3682323
  simp only [CollatzResearch.WordTrace]
  refine ⟨134305353438580136544963623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89536902292386757696642415 134305353438580136544963623)
  ·
    refine ⟨201458030157870204817445435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134305353438580136544963623 201458030157870204817445435)
    ·
      refine ⟨302187045236805307226168153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201458030157870204817445435 302187045236805307226168153)
      ·
        refine ⟨226640283927603980419626115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302187045236805307226168153 226640283927603980419626115)
        ·
          refine ⟨339960425891405970629439173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226640283927603980419626115 339960425891405970629439173)
          ·
            refine ⟨63742579854638619493019845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339960425891405970629439173 63742579854638619493019845)
            ·
              refine ⟨11951733722744741154941221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63742579854638619493019845 11951733722744741154941221)
              ·
                refine ⟨2240950073014638966551479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11951733722744741154941221 2240950073014638966551479)
                ·
                  refine ⟨3361425109521958449827219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2240950073014638966551479 3361425109521958449827219)
                  ·
                    refine ⟨5042137664282937674740829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3361425109521958449827219 5042137664282937674740829)
                    ·
                      refine ⟨1890801624106101628027811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5042137664282937674740829 1890801624106101628027811)
                      ·
                        rfl

theorem cell23_3682323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 1, 1, 3].length) (baseStart_3682323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682323 prefixEnd_3682323 := by exact prefixLift 3682323
  have htrace : WordTrace (prefixWord ++ tailWord_3682323) baseStart_3682323 baseEnd_3682323 := by
    simpa [prefixWord, tailWord_3682323, baseEnd_3682323] using wordTrace_append hprefix tailTrace_3682323
  have hstable : (prefixWord ++ tailWord_3682323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682323).length < 2 ^ (prefixWord ++ tailWord_3682323).sum := by decide
  have hdescent : baseEnd_3682323 < baseStart_3682323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682359 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 4]
def baseStart_3682359 : Nat := 118140960795 + 3682359 * 2 ^ 59
def prefixEnd_3682359 : Nat := 4983230072969 + 3 ^ 40 * 3682359 * 2
def baseEnd_3682359 : Nat := 1890820109409663487177645

theorem tailTrace_3682359 : CollatzResearch.WordTrace tailWord_3682359 prefixEnd_3682359 1890820109409663487177645 := by
  unfold tailWord_3682359
  simp only [CollatzResearch.WordTrace]
  refine ⟨134306666466449714693274131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89537777644299809795516087 134306666466449714693274131)
  ·
    refine ⟨201459999699674572039911197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134306666466449714693274131 201459999699674572039911197)
    ·
      refine ⟨75547499887377964514966699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201459999699674572039911197 75547499887377964514966699)
      ·
        refine ⟨113321249831066946772450049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75547499887377964514966699 113321249831066946772450049)
        ·
          refine ⟨84990937373300210079337537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113321249831066946772450049 84990937373300210079337537)
          ·
            refine ⟨63743203029975157559503153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84990937373300210079337537 63743203029975157559503153)
            ·
              refine ⟨47807402272481368169627365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63743203029975157559503153 47807402272481368169627365)
              ·
                refine ⟨8963887926090256531805131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47807402272481368169627365 8963887926090256531805131)
                ·
                  refine ⟨13445831889135384797707697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8963887926090256531805131 13445831889135384797707697)
                  ·
                    refine ⟨10084373916851538598280773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13445831889135384797707697 10084373916851538598280773)
                    ·
                      refine ⟨1890820109409663487177645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10084373916851538598280773 1890820109409663487177645)
                      ·
                        rfl

theorem cell23_3682359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_3682359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682359 prefixEnd_3682359 := by exact prefixLift 3682359
  have htrace : WordTrace (prefixWord ++ tailWord_3682359) baseStart_3682359 baseEnd_3682359 := by
    simpa [prefixWord, tailWord_3682359, baseEnd_3682359] using wordTrace_append hprefix tailTrace_3682359
  have hstable : (prefixWord ++ tailWord_3682359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682359).length < 2 ^ (prefixWord ++ tailWord_3682359).sum := by decide
  have hdescent : baseEnd_3682359 < baseStart_3682359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682369 : List Nat := [1, 2, 5, 1, 2, 1, 11]
def baseStart_3682369 : Nat := 118140960795 + 3682369 * 2 ^ 59
def prefixEnd_3682369 : Nat := 4983230072969 + 3 ^ 40 * 3682369 * 2
def baseEnd_3682369 : Nat := 23343521533533437630279

theorem tailTrace_3682369 : CollatzResearch.WordTrace tailWord_3682369 prefixEnd_3682369 23343521533533437630279 := by
  unfold tailWord_3682369
  simp only [CollatzResearch.WordTrace]
  refine ⟨134307031196413486401138161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89538020797608990934092107 134307031196413486401138161)
  ·
    refine ⟨100730273397310114800853621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134307031196413486401138161 100730273397310114800853621)
    ·
      refine ⟨9443463130997823262580027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100730273397310114800853621 9443463130997823262580027)
      ·
        refine ⟨14165194696496734893870041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9443463130997823262580027 14165194696496734893870041)
        ·
          refine ⟨10623896022372551170402531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14165194696496734893870041 10623896022372551170402531)
          ·
            refine ⟨15935844033558826755603797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10623896022372551170402531 15935844033558826755603797)
            ·
              refine ⟨23343521533533437630279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 15935844033558826755603797 23343521533533437630279)
              ·
                rfl

theorem cell23_3682369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 11].length) (baseStart_3682369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682369 prefixEnd_3682369 := by exact prefixLift 3682369
  have htrace : WordTrace (prefixWord ++ tailWord_3682369) baseStart_3682369 baseEnd_3682369 := by
    simpa [prefixWord, tailWord_3682369, baseEnd_3682369] using wordTrace_append hprefix tailTrace_3682369
  have hstable : (prefixWord ++ tailWord_3682369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682369).length < 2 ^ (prefixWord ++ tailWord_3682369).sum := by decide
  have hdescent : baseEnd_3682369 < baseStart_3682369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682374 : List Nat := [6, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_3682374 : Nat := 118140960795 + 3682374 * 2 ^ 59
def prefixEnd_3682374 : Nat := 4983230072969 + 3 ^ 40 * 3682374 * 2
def baseEnd_3682374 : Nat := 1890827811619480928490077

theorem tailTrace_3682374 : CollatzResearch.WordTrace tailWord_3682374 prefixEnd_3682374 1890827811619480928490077 := by
  unfold tailWord_3682374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4197100423793605382970943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89538142374263581503380117 4197100423793605382970943)
  ·
    refine ⟨6295650635690408074456415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4197100423793605382970943 6295650635690408074456415)
    ·
      refine ⟨9443475953535612111684623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6295650635690408074456415 9443475953535612111684623)
      ·
        refine ⟨14165213930303418167526935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9443475953535612111684623 14165213930303418167526935)
        ·
          refine ⟨21247820895455127251290403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14165213930303418167526935 21247820895455127251290403)
          ·
            refine ⟨31871731343182690876935605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21247820895455127251290403 31871731343182690876935605)
            ·
              refine ⟨2987974813423377269712713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31871731343182690876935605 2987974813423377269712713)
              ·
                refine ⟨2240981110067532952284535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2987974813423377269712713 2240981110067532952284535)
                ·
                  refine ⟨3361471665101299428426803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2240981110067532952284535 3361471665101299428426803)
                  ·
                    refine ⟨5042207497651949142640205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3361471665101299428426803 5042207497651949142640205)
                    ·
                      refine ⟨1890827811619480928490077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5042207497651949142640205 1890827811619480928490077)
                      ·
                        rfl

theorem cell23_3682374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_3682374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682374 prefixEnd_3682374 := by exact prefixLift 3682374
  have htrace : WordTrace (prefixWord ++ tailWord_3682374) baseStart_3682374 baseEnd_3682374 := by
    simpa [prefixWord, tailWord_3682374, baseEnd_3682374] using wordTrace_append hprefix tailTrace_3682374
  have hstable : (prefixWord ++ tailWord_3682374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682374).length < 2 ^ (prefixWord ++ tailWord_3682374).sum := by decide
  have hdescent : baseEnd_3682374 < baseStart_3682374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682379 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 3]
def baseStart_3682379 : Nat := 118140960795 + 3682379 * 2 ^ 59
def prefixEnd_3682379 : Nat := 4983230072969 + 3 ^ 40 * 3682379 * 2
def baseEnd_3682379 : Nat := 1890830379022753408927553

theorem tailTrace_3682379 : CollatzResearch.WordTrace tailWord_3682379 prefixEnd_3682379 1890830379022753408927553 := by
  unfold tailWord_3682379
  simp only [CollatzResearch.WordTrace]
  refine ⟨134307395926377258109002191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89538263950918172072668127 134307395926377258109002191)
  ·
    refine ⟨201461093889565887163503287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134307395926377258109002191 201461093889565887163503287)
    ·
      refine ⟨302191640834348830745254931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201461093889565887163503287 302191640834348830745254931)
      ·
        refine ⟨453287461251523246117882397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302191640834348830745254931 453287461251523246117882397)
        ·
          refine ⟨169982797969321217294205899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453287461251523246117882397 169982797969321217294205899)
          ·
            refine ⟨254974196953981825941308849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169982797969321217294205899 254974196953981825941308849)
            ·
              refine ⟨191230647715486369455981637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254974196953981825941308849 191230647715486369455981637)
              ·
                refine ⟨35855746446653694272996557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191230647715486369455981637 35855746446653694272996557)
                ·
                  refine ⟨13445904917495135352373709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35855746446653694272996557 13445904917495135352373709)
                  ·
                    refine ⟨5042214344060675757140141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13445904917495135352373709 5042214344060675757140141)
                    ·
                      refine ⟨1890830379022753408927553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5042214344060675757140141 1890830379022753408927553)
                      ·
                        rfl

theorem cell23_3682379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 3].length) (baseStart_3682379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682379 prefixEnd_3682379 := by exact prefixLift 3682379
  have htrace : WordTrace (prefixWord ++ tailWord_3682379) baseStart_3682379 baseEnd_3682379 := by
    simpa [prefixWord, tailWord_3682379, baseEnd_3682379] using wordTrace_append hprefix tailTrace_3682379
  have hstable : (prefixWord ++ tailWord_3682379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682379).length < 2 ^ (prefixWord ++ tailWord_3682379).sum := by decide
  have hdescent : baseEnd_3682379 < baseStart_3682379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682380 : List Nat := [2, 2, 1, 3, 1, 1, 2, 6, 1, 2, 2]
def baseStart_3682380 : Nat := 118140960795 + 3682380 * 2 ^ 59
def prefixEnd_3682380 : Nat := 4983230072969 + 3 ^ 40 * 3682380 * 2
def baseEnd_3682380 : Nat := 1890830892503407905015049

theorem tailTrace_3682380 : CollatzResearch.WordTrace tailWord_3682380 prefixEnd_3682380 1890830892503407905015049 := by
  unfold tailWord_3682380
  simp only [CollatzResearch.WordTrace]
  refine ⟨67153716199686817639894297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89538288266249090186525729 67153716199686817639894297)
  ·
    refine ⟨50365287149765113229920723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67153716199686817639894297 50365287149765113229920723)
    ·
      refine ⟨75547930724647669844881085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50365287149765113229920723 75547930724647669844881085)
      ·
        refine ⟨28330474021742876191830407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75547930724647669844881085 28330474021742876191830407)
        ·
          refine ⟨42495711032614314287745611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28330474021742876191830407 42495711032614314287745611)
          ·
            refine ⟨63743566548921471431618417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42495711032614314287745611 63743566548921471431618417)
            ·
              refine ⟨47807674911691103573713813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63743566548921471431618417 47807674911691103573713813)
              ·
                refine ⟨2240984761485520480017835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47807674911691103573713813 2240984761485520480017835)
                ·
                  refine ⟨3361477142228280720026753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2240984761485520480017835 3361477142228280720026753)
                  ·
                    refine ⟨2521107856671210540020065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3361477142228280720026753 2521107856671210540020065)
                    ·
                      refine ⟨1890830892503407905015049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2521107856671210540020065 1890830892503407905015049)
                      ·
                        rfl

theorem cell23_3682380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_3682380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682380 prefixEnd_3682380 := by exact prefixLift 3682380
  have htrace : WordTrace (prefixWord ++ tailWord_3682380) baseStart_3682380 baseEnd_3682380 := by
    simpa [prefixWord, tailWord_3682380, baseEnd_3682380] using wordTrace_append hprefix tailTrace_3682380
  have hstable : (prefixWord ++ tailWord_3682380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682380).length < 2 ^ (prefixWord ++ tailWord_3682380).sum := by decide
  have hdescent : baseEnd_3682380 < baseStart_3682380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682386 : List Nat := [3, 2, 2, 1, 4, 1, 2, 8]
def baseStart_3682386 : Nat := 118140960795 + 3682386 * 2 ^ 59
def prefixEnd_3682386 : Nat := 4983230072969 + 3 ^ 40 * 3682386 * 2
def baseEnd_3682386 : Nat := 70030887903234625242223

theorem tailTrace_3682386 : CollatzResearch.WordTrace tailWord_3682386 prefixEnd_3682386 70030887903234625242223 := by
  unfold tailWord_3682386
  simp only [CollatzResearch.WordTrace]
  refine ⟨33576912809337974576126753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89538434158234598869671341 33576912809337974576126753)
  ·
    refine ⟨25182684607003480932095065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33576912809337974576126753 25182684607003480932095065)
    ·
      refine ⟨18887013455252610699071299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25182684607003480932095065 18887013455252610699071299)
      ·
        refine ⟨28330520182878916048606949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18887013455252610699071299 28330520182878916048606949)
        ·
          refine ⟨5311972534289796759113803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28330520182878916048606949 5311972534289796759113803)
          ·
            refine ⟨7967958801434695138670705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5311972534289796759113803 7967958801434695138670705)
            ·
              refine ⟨5975969101076021354003029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7967958801434695138670705 5975969101076021354003029)
              ·
                refine ⟨70030887903234625242223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5975969101076021354003029 70030887903234625242223)
                ·
                  rfl

theorem cell23_3682386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 8].length) (baseStart_3682386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682386 prefixEnd_3682386 := by exact prefixLift 3682386
  have htrace : WordTrace (prefixWord ++ tailWord_3682386) baseStart_3682386 baseEnd_3682386 := by
    simpa [prefixWord, tailWord_3682386, baseEnd_3682386] using wordTrace_append hprefix tailTrace_3682386
  have hstable : (prefixWord ++ tailWord_3682386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682386).length < 2 ^ (prefixWord ++ tailWord_3682386).sum := by decide
  have hdescent : baseEnd_3682386 < baseStart_3682386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682439 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_3682439 : Nat := 118140960795 + 3682439 * 2 ^ 59
def prefixEnd_3682439 : Nat := 4983230072969 + 3 ^ 40 * 3682439 * 2
def baseEnd_3682439 : Nat := 1890861187862023174177277

theorem tailTrace_3682439 : CollatzResearch.WordTrace tailWord_3682439 prefixEnd_3682439 1890861187862023174177277 := by
  unfold tailWord_3682439
  simp only [CollatzResearch.WordTrace]
  refine ⟨134309584306159888356186371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89539722870773258904124247 134309584306159888356186371)
  ·
    refine ⟨201464376459239832534279557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134309584306159888356186371 201464376459239832534279557)
    ·
      refine ⟨37774570586107468600177417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201464376459239832534279557 37774570586107468600177417)
      ·
        refine ⟨28330927939580601450133063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37774570586107468600177417 28330927939580601450133063)
        ·
          refine ⟨42496391909370902175199595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28330927939580601450133063 42496391909370902175199595)
          ·
            refine ⟨63744587864056353262799393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42496391909370902175199595 63744587864056353262799393)
            ·
              refine ⟨47808440898042264947099545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63744587864056353262799393 47808440898042264947099545)
              ·
                refine ⟨35856330673531698710324659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47808440898042264947099545 35856330673531698710324659)
                ·
                  refine ⟨53784496010297548065486989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35856330673531698710324659 53784496010297548065486989)
                  ·
                    refine ⟨20169186003861580524557621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53784496010297548065486989 20169186003861580524557621)
                    ·
                      refine ⟨1890861187862023174177277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20169186003861580524557621 1890861187862023174177277)
                      ·
                        rfl

theorem cell23_3682439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_3682439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682439 prefixEnd_3682439 := by exact prefixLift 3682439
  have htrace : WordTrace (prefixWord ++ tailWord_3682439) baseStart_3682439 baseEnd_3682439 := by
    simpa [prefixWord, tailWord_3682439, baseEnd_3682439] using wordTrace_append hprefix tailTrace_3682439
  have hstable : (prefixWord ++ tailWord_3682439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682439).length < 2 ^ (prefixWord ++ tailWord_3682439).sum := by decide
  have hdescent : baseEnd_3682439 < baseStart_3682439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682453 : List Nat := [1, 3, 2, 1, 1, 1, 6, 1, 1, 4, 2]
def baseStart_3682453 : Nat := 118140960795 + 3682453 * 2 ^ 59
def prefixEnd_3682453 : Nat := 4983230072969 + 3 ^ 40 * 3682453 * 2
def baseEnd_3682453 : Nat := 1890868376591186119402213

theorem tailTrace_3682453 : CollatzResearch.WordTrace tailWord_3682453 prefixEnd_3682453 1890868376591186119402213 := by
  unfold tailWord_3682453
  simp only [CollatzResearch.WordTrace]
  refine ⟨134310094928109168747196013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89540063285406112498130675 134310094928109168747196013)
  ·
    refine ⟨50366285598040938280198505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134310094928109168747196013 50366285598040938280198505)
    ·
      refine ⟨37774714198530703710148879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50366285598040938280198505 37774714198530703710148879)
      ·
        refine ⟨56662071297796055565223319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37774714198530703710148879 56662071297796055565223319)
        ·
          refine ⟨84993106946694083347834979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56662071297796055565223319 84993106946694083347834979)
          ·
            refine ⟨127489660420041125021752469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84993106946694083347834979 127489660420041125021752469)
            ·
              refine ⟨5976077832189427735394647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127489660420041125021752469 5976077832189427735394647)
              ·
                refine ⟨8964116748284141603091971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5976077832189427735394647 8964116748284141603091971)
                ·
                  refine ⟨13446175122426212404637957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8964116748284141603091971 13446175122426212404637957)
                  ·
                    refine ⟨2521157835454914825869617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13446175122426212404637957 2521157835454914825869617)
                    ·
                      refine ⟨1890868376591186119402213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2521157835454914825869617 1890868376591186119402213)
                      ·
                        rfl

theorem cell23_3682453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_3682453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682453 prefixEnd_3682453 := by exact prefixLift 3682453
  have htrace : WordTrace (prefixWord ++ tailWord_3682453) baseStart_3682453 baseEnd_3682453 := by
    simpa [prefixWord, tailWord_3682453, baseEnd_3682453] using wordTrace_append hprefix tailTrace_3682453
  have hstable : (prefixWord ++ tailWord_3682453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682453).length < 2 ^ (prefixWord ++ tailWord_3682453).sum := by decide
  have hdescent : baseEnd_3682453 < baseStart_3682453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682454 : List Nat := [5, 3, 2, 1, 1, 1, 3, 7]
def baseStart_3682454 : Nat := 118140960795 + 3682454 * 2 ^ 59
def prefixEnd_3682454 : Nat := 4983230072969 + 3 ^ 40 * 3682454 * 2
def baseEnd_3682454 : Nat := 70032181113771874647767

theorem tailTrace_3682454 : CollatzResearch.WordTrace tailWord_3682454 prefixEnd_3682454 70032181113771874647767 := by
  unfold tailWord_3682454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8394383212569096619873901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89540087600737030611988277 8394383212569096619873901)
  ·
    refine ⟨3147893704713411232452713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8394383212569096619873901 3147893704713411232452713)
    ·
      refine ⟨2360920278535058424339535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3147893704713411232452713 2360920278535058424339535)
      ·
        refine ⟨3541380417802587636509303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2360920278535058424339535 3541380417802587636509303)
        ·
          refine ⟨5312070626703881454763955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3541380417802587636509303 5312070626703881454763955)
          ·
            refine ⟨7968105940055822182145933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5312070626703881454763955 7968105940055822182145933)
            ·
              refine ⟨2988039727520933318304725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7968105940055822182145933 2988039727520933318304725)
              ·
                refine ⟨70032181113771874647767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2988039727520933318304725 70032181113771874647767)
                ·
                  rfl

theorem cell23_3682454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_3682454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682454 prefixEnd_3682454 := by exact prefixLift 3682454
  have htrace : WordTrace (prefixWord ++ tailWord_3682454) baseStart_3682454 baseEnd_3682454 := by
    simpa [prefixWord, tailWord_3682454, baseEnd_3682454] using wordTrace_append hprefix tailTrace_3682454
  have hstable : (prefixWord ++ tailWord_3682454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682454).length < 2 ^ (prefixWord ++ tailWord_3682454).sum := by decide
  have hdescent : baseEnd_3682454 < baseStart_3682454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682487 : List Nat := [1, 1, 3, 1, 4, 4, 1, 2, 2, 2, 2]
def baseStart_3682487 : Nat := 118140960795 + 3682487 * 2 ^ 59
def prefixEnd_3682487 : Nat := 4983230072969 + 3 ^ 40 * 3682487 * 2
def baseEnd_3682487 : Nat := 1890885834933438986377057

theorem tailTrace_3682487 : CollatzResearch.WordTrace tailWord_3682487 prefixEnd_3682487 1890885834933438986377057 := by
  unfold tailWord_3682487
  simp only [CollatzResearch.WordTrace]
  refine ⟨134311335009985992553933715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89540890006657328369289143 134311335009985992553933715)
  ·
    refine ⟨201467002514978988830900573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134311335009985992553933715 201467002514978988830900573)
    ·
      refine ⟨75550125943117120811587715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201467002514978988830900573 75550125943117120811587715)
      ·
        refine ⟨113325188914675681217381573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75550125943117120811587715 113325188914675681217381573)
        ·
          refine ⟨21248472921501690228259045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113325188914675681217381573 21248472921501690228259045)
          ·
            refine ⟨3984088672781566917798571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21248472921501690228259045 3984088672781566917798571)
            ·
              refine ⟨5976133009172350376697857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3984088672781566917798571 5976133009172350376697857)
              ·
                refine ⟨4482099756879262782523393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5976133009172350376697857 4482099756879262782523393)
                ·
                  refine ⟨3361574817659447086892545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4482099756879262782523393 3361574817659447086892545)
                  ·
                    refine ⟨2521181113244585315169409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3361574817659447086892545 2521181113244585315169409)
                    ·
                      refine ⟨1890885834933438986377057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2521181113244585315169409 1890885834933438986377057)
                      ·
                        rfl

theorem cell23_3682487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 2, 2, 2, 2].length) (baseStart_3682487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682487 prefixEnd_3682487 := by exact prefixLift 3682487
  have htrace : WordTrace (prefixWord ++ tailWord_3682487) baseStart_3682487 baseEnd_3682487 := by
    simpa [prefixWord, tailWord_3682487, baseEnd_3682487] using wordTrace_append hprefix tailTrace_3682487
  have hstable : (prefixWord ++ tailWord_3682487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682487).length < 2 ^ (prefixWord ++ tailWord_3682487).sum := by decide
  have hdescent : baseEnd_3682487 < baseStart_3682487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682499 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 5]
def baseStart_3682499 : Nat := 118140960795 + 3682499 * 2 ^ 59
def prefixEnd_3682499 : Nat := 4983230072969 + 3 ^ 40 * 3682499 * 2
def baseEnd_3682499 : Nat := 1890891996701292939427001

theorem tailTrace_3682499 : CollatzResearch.WordTrace tailWord_3682499 prefixEnd_3682499 1890891996701292939427001 := by
  unfold tailWord_3682499
  simp only [CollatzResearch.WordTrace]
  refine ⟨134311772685942518603370551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89541181790628345735580367 134311772685942518603370551)
  ·
    refine ⟨201467659028913777905055827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134311772685942518603370551 201467659028913777905055827)
    ·
      refine ⟨302201488543370666857583741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201467659028913777905055827 302201488543370666857583741)
      ·
        refine ⟨113325558203764000071593903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302201488543370666857583741 113325558203764000071593903)
        ·
          refine ⟨169988337305646000107390855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113325558203764000071593903 169988337305646000107390855)
          ·
            refine ⟨254982505958469000161086283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169988337305646000107390855 254982505958469000161086283)
            ·
              refine ⟨382473758937703500241629425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254982505958469000161086283 382473758937703500241629425)
              ·
                refine ⟨286855319203277625181222069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382473758937703500241629425 286855319203277625181222069)
                ·
                  refine ⟨26892686175307277360739569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 286855319203277625181222069 26892686175307277360739569)
                  ·
                    refine ⟨20169514631480458020554677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26892686175307277360739569 20169514631480458020554677)
                    ·
                      refine ⟨1890891996701292939427001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20169514631480458020554677 1890891996701292939427001)
                      ·
                        rfl

theorem cell23_3682499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_3682499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682499 prefixEnd_3682499 := by exact prefixLift 3682499
  have htrace : WordTrace (prefixWord ++ tailWord_3682499) baseStart_3682499 baseEnd_3682499 := by
    simpa [prefixWord, tailWord_3682499, baseEnd_3682499] using wordTrace_append hprefix tailTrace_3682499
  have hstable : (prefixWord ++ tailWord_3682499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682499).length < 2 ^ (prefixWord ++ tailWord_3682499).sum := by decide
  have hdescent : baseEnd_3682499 < baseStart_3682499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682519 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 1, 10]
def baseStart_3682519 : Nat := 118140960795 + 3682519 * 2 ^ 59
def prefixEnd_3682519 : Nat := 4983230072969 + 3 ^ 40 * 3682519 * 2
def baseEnd_3682519 : Nat := 630300755438127620392303

theorem tailTrace_3682519 : CollatzResearch.WordTrace tailWord_3682519 prefixEnd_3682519 630300755438127620392303 := by
  unfold tailWord_3682519
  simp only [CollatzResearch.WordTrace]
  refine ⟨134312502145870062019098611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89541668097246708012732407 134312502145870062019098611)
  ·
    refine ⟨201468753218805093028647917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134312502145870062019098611 201468753218805093028647917)
    ·
      refine ⟨75550782457051909885742969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201468753218805093028647917 75550782457051909885742969)
      ·
        refine ⟨56663086842788932414307227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75550782457051909885742969 56663086842788932414307227)
        ·
          refine ⟨84994630264183398621460841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56663086842788932414307227 84994630264183398621460841)
          ·
            refine ⟨63745972698137548966095631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84994630264183398621460841 63745972698137548966095631)
            ·
              refine ⟨95618959047206323449143447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63745972698137548966095631 95618959047206323449143447)
              ·
                refine ⟨143428438570809485173715171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95618959047206323449143447 143428438570809485173715171)
                ·
                  refine ⟨215142657856214227760572757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143428438570809485173715171 215142657856214227760572757)
                  ·
                    refine ⟨630300755438127620392303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 215142657856214227760572757 630300755438127620392303)
                    ·
                      rfl

theorem cell23_3682519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_3682519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682519 prefixEnd_3682519 := by exact prefixLift 3682519
  have htrace : WordTrace (prefixWord ++ tailWord_3682519) baseStart_3682519 baseEnd_3682519 := by
    simpa [prefixWord, tailWord_3682519, baseEnd_3682519] using wordTrace_append hprefix tailTrace_3682519
  have hstable : (prefixWord ++ tailWord_3682519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682519).length < 2 ^ (prefixWord ++ tailWord_3682519).sum := by decide
  have hdescent : baseEnd_3682519 < baseStart_3682519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682543 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 4]
def baseStart_3682543 : Nat := 118140960795 + 3682543 * 2 ^ 59
def prefixEnd_3682543 : Nat := 4983230072969 + 3 ^ 40 * 3682543 * 2
def baseEnd_3682543 : Nat := 1890914589850090767276799

theorem tailTrace_3682543 : CollatzResearch.WordTrace tailWord_3682543 prefixEnd_3682543 1890914589850090767276799 := by
  unfold tailWord_3682543
  simp only [CollatzResearch.WordTrace]
  refine ⟨134313377497783114117972283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89542251665188742745314855 134313377497783114117972283)
  ·
    refine ⟨201470066246674671176958425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134313377497783114117972283 201470066246674671176958425)
    ·
      refine ⟨151102549685006003382718819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201470066246674671176958425 151102549685006003382718819)
      ·
        refine ⟨226653824527509005074078229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151102549685006003382718819 226653824527509005074078229)
        ·
          refine ⟨10624398024726984612847417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 226653824527509005074078229 10624398024726984612847417)
          ·
            refine ⟨7968298518545238459635563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10624398024726984612847417 7968298518545238459635563)
            ·
              refine ⟨11952447777817857689453345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7968298518545238459635563 11952447777817857689453345)
              ·
                refine ⟨8964335833363393267090009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11952447777817857689453345 8964335833363393267090009)
                ·
                  refine ⟨6723251875022544950317507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8964335833363393267090009 6723251875022544950317507)
                  ·
                    refine ⟨10084877812533817425476261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6723251875022544950317507 10084877812533817425476261)
                    ·
                      refine ⟨1890914589850090767276799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10084877812533817425476261 1890914589850090767276799)
                      ·
                        rfl

theorem cell23_3682543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_3682543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682543 prefixEnd_3682543 := by exact prefixLift 3682543
  have htrace : WordTrace (prefixWord ++ tailWord_3682543) baseStart_3682543 baseEnd_3682543 := by
    simpa [prefixWord, tailWord_3682543, baseEnd_3682543] using wordTrace_append hprefix tailTrace_3682543
  have hstable : (prefixWord ++ tailWord_3682543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682543).length < 2 ^ (prefixWord ++ tailWord_3682543).sum := by decide
  have hdescent : baseEnd_3682543 < baseStart_3682543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682600 : List Nat := [2, 1, 5, 1, 3, 1, 2, 2, 6]
def baseStart_3682600 : Nat := 118140960795 + 3682600 * 2 ^ 59
def prefixEnd_3682600 : Nat := 4983230072969 + 3 ^ 40 * 3682600 * 2
def baseEnd_3682600 : Nat := 210104873138599671584893

theorem tailTrace_3682600 : CollatzResearch.WordTrace tailWord_3682600 prefixEnd_3682600 210104873138599671584893 := by
  unfold tailWord_3682600
  simp only [CollatzResearch.WordTrace]
  refine ⟨67157728229288306426398627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89543637639051075235198169 67157728229288306426398627)
  ·
    refine ⟨100736592343932459639597941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67157728229288306426398627 100736592343932459639597941)
    ·
      refine ⟨9444055532243668091212307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100736592343932459639597941 9444055532243668091212307)
      ·
        refine ⟨14166083298365502136818461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9444055532243668091212307 14166083298365502136818461)
        ·
          refine ⟨5312281236887063301306923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14166083298365502136818461 5312281236887063301306923)
          ·
            refine ⟨7968421855330594951960385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5312281236887063301306923 7968421855330594951960385)
            ·
              refine ⟨5976316391497946213970289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7968421855330594951960385 5976316391497946213970289)
              ·
                refine ⟨4482237293623459660477717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5976316391497946213970289 4482237293623459660477717)
                ·
                  refine ⟨210104873138599671584893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4482237293623459660477717 210104873138599671584893)
                  ·
                    rfl

theorem cell23_3682600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 6].length) (baseStart_3682600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682600 prefixEnd_3682600 := by exact prefixLift 3682600
  have htrace : WordTrace (prefixWord ++ tailWord_3682600) baseStart_3682600 baseEnd_3682600 := by
    simpa [prefixWord, tailWord_3682600, baseEnd_3682600] using wordTrace_append hprefix tailTrace_3682600
  have hstable : (prefixWord ++ tailWord_3682600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682600).length < 2 ^ (prefixWord ++ tailWord_3682600).sum := by decide
  have hdescent : baseEnd_3682600 < baseStart_3682600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682633 : List Nat := [1, 2, 1, 1, 2, 3, 1, 6, 1, 1, 4]
def baseStart_3682633 : Nat := 118140960795 + 3682633 * 2 ^ 59
def prefixEnd_3682633 : Nat := 4983230072969 + 3 ^ 40 * 3682633 * 2
def baseEnd_3682633 : Nat := 1890960803108995415151385

theorem tailTrace_3682633 : CollatzResearch.WordTrace tailWord_3682633 prefixEnd_3682633 1890960803108995415151385 := by
  unfold tailWord_3682633
  simp only [CollatzResearch.WordTrace]
  refine ⟨134316660067457059488748553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89544440044971372992499035 134316660067457059488748553)
  ·
    refine ⟨100737495050592794616561415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134316660067457059488748553 100737495050592794616561415)
    ·
      refine ⟨151106242575889191924842123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100737495050592794616561415 151106242575889191924842123)
      ·
        refine ⟨226659363863833787887263185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151106242575889191924842123 226659363863833787887263185)
        ·
          refine ⟨169994522897875340915447389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226659363863833787887263185 169994522897875340915447389)
          ·
            refine ⟨63747946086703252843292771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169994522897875340915447389 63747946086703252843292771)
            ·
              refine ⟨95621919130054879264939157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63747946086703252843292771 95621919130054879264939157)
              ·
                refine ⟨4482277459221322465544023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95621919130054879264939157 4482277459221322465544023)
                ·
                  refine ⟨6723416188831983698316035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4482277459221322465544023 6723416188831983698316035)
                  ·
                    refine ⟨10085124283247975547474053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6723416188831983698316035 10085124283247975547474053)
                    ·
                      refine ⟨1890960803108995415151385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10085124283247975547474053 1890960803108995415151385)
                      ·
                        rfl

theorem cell23_3682633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 1, 1, 4].length) (baseStart_3682633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682633 prefixEnd_3682633 := by exact prefixLift 3682633
  have htrace : WordTrace (prefixWord ++ tailWord_3682633) baseStart_3682633 baseEnd_3682633 := by
    simpa [prefixWord, tailWord_3682633, baseEnd_3682633] using wordTrace_append hprefix tailTrace_3682633
  have hstable : (prefixWord ++ tailWord_3682633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682633).length < 2 ^ (prefixWord ++ tailWord_3682633).sum := by decide
  have hdescent : baseEnd_3682633 < baseStart_3682633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682644 : List Nat := [2, 4, 1, 1, 2, 3, 2, 3, 1, 1, 3]
def baseStart_3682644 : Nat := 118140960795 + 3682644 * 2 ^ 59
def prefixEnd_3682644 : Nat := 4983230072969 + 3 ^ 40 * 3682644 * 2
def baseEnd_3682644 : Nat := 1890966451396194872113835

theorem tailTrace_3682644 : CollatzResearch.WordTrace tailWord_3682644 prefixEnd_3682644 1890966451396194872113835 := by
  unfold tailWord_3682644
  simp only [CollatzResearch.WordTrace]
  refine ⟨67158530635208604183699493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89544707513611472244932657 67158530635208604183699493)
  ·
    refine ⟨12592224494101613284443655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67158530635208604183699493 12592224494101613284443655)
    ·
      refine ⟨18888336741152419926665483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12592224494101613284443655 18888336741152419926665483)
      ·
        refine ⟨28332505111728629889998225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18888336741152419926665483 28332505111728629889998225)
        ·
          refine ⟨21249378833796472417498669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28332505111728629889998225 21249378833796472417498669)
          ·
            refine ⟨7968517062673677156562001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21249378833796472417498669 7968517062673677156562001)
            ·
              refine ⟨5976387797005257867421501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7968517062673677156562001 5976387797005257867421501)
              ·
                refine ⟨2241145423876971700283063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5976387797005257867421501 2241145423876971700283063)
                ·
                  refine ⟨3361718135815457550424595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2241145423876971700283063 3361718135815457550424595)
                  ·
                    refine ⟨5042577203723186325636893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3361718135815457550424595 5042577203723186325636893)
                    ·
                      refine ⟨1890966451396194872113835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5042577203723186325636893 1890966451396194872113835)
                      ·
                        rfl

theorem cell23_3682644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_3682644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682644 prefixEnd_3682644 := by exact prefixLift 3682644
  have htrace : WordTrace (prefixWord ++ tailWord_3682644) baseStart_3682644 baseEnd_3682644 := by
    simpa [prefixWord, tailWord_3682644, baseEnd_3682644] using wordTrace_append hprefix tailTrace_3682644
  have hstable : (prefixWord ++ tailWord_3682644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682644).length < 2 ^ (prefixWord ++ tailWord_3682644).sum := by decide
  have hdescent : baseEnd_3682644 < baseStart_3682644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682650 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2]
def baseStart_3682650 : Nat := 118140960795 + 3682650 * 2 ^ 59
def prefixEnd_3682650 : Nat := 4983230072969 + 3 ^ 40 * 3682650 * 2
def baseEnd_3682650 : Nat := 1890969532280121848638807

theorem tailTrace_3682650 : CollatzResearch.WordTrace tailWord_3682650 prefixEnd_3682650 1890969532280121848638807 := by
  unfold tailWord_3682650
  simp only [CollatzResearch.WordTrace]
  refine ⟨33579320027098867848029351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89544853405596980928078269 33579320027098867848029351)
  ·
    refine ⟨50368980040648301772044027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33579320027098867848029351 50368980040648301772044027)
    ·
      refine ⟨75553470060972452658066041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50368980040648301772044027 75553470060972452658066041)
      ·
        refine ⟨56665102545729339493549531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75553470060972452658066041 56665102545729339493549531)
        ·
          refine ⟨84997653818594009240324297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56665102545729339493549531 84997653818594009240324297)
          ·
            refine ⟨63748240363945506930243223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84997653818594009240324297 63748240363945506930243223)
            ·
              refine ⟨95622360545918260395364835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63748240363945506930243223 95622360545918260395364835)
              ·
                refine ⟨143433540818877390593047253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95622360545918260395364835 143433540818877390593047253)
                ·
                  refine ⟨3361723612942438842024545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 143433540818877390593047253 3361723612942438842024545)
                  ·
                    refine ⟨2521292709706829131518409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3361723612942438842024545 2521292709706829131518409)
                    ·
                      refine ⟨1890969532280121848638807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2521292709706829131518409 1890969532280121848638807)
                      ·
                        rfl

theorem cell23_3682650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_3682650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682650 prefixEnd_3682650 := by exact prefixLift 3682650
  have htrace : WordTrace (prefixWord ++ tailWord_3682650) baseStart_3682650 baseEnd_3682650 := by
    simpa [prefixWord, tailWord_3682650, baseEnd_3682650] using wordTrace_append hprefix tailTrace_3682650
  have hstable : (prefixWord ++ tailWord_3682650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682650).length < 2 ^ (prefixWord ++ tailWord_3682650).sum := by decide
  have hdescent : baseEnd_3682650 < baseStart_3682650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682700 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 4, 1, 3]
def baseStart_3682700 : Nat := 118140960795 + 3682700 * 2 ^ 59
def prefixEnd_3682700 : Nat := 4983230072969 + 3 ^ 40 * 3682700 * 2
def baseEnd_3682700 : Nat := 1890995206312846653013577

theorem tailTrace_3682700 : CollatzResearch.WordTrace tailWord_3682700 prefixEnd_3682700 1890995206312846653013577 := by
  unfold tailWord_3682700
  simp only [CollatzResearch.WordTrace]
  refine ⟨67159551879107164965718777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89546069172142886620958369 67159551879107164965718777)
  ·
    refine ⟨50369663909330373724289083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67159551879107164965718777 50369663909330373724289083)
    ·
      refine ⟨75554495863995560586433625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50369663909330373724289083 75554495863995560586433625)
      ·
        refine ⟨56665871897996670439825219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75554495863995560586433625 56665871897996670439825219)
        ·
          refine ⟨84998807846995005659737829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56665871897996670439825219 84998807846995005659737829)
          ·
            refine ⟨15937276471311563561200843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84998807846995005659737829 15937276471311563561200843)
            ·
              refine ⟨23905914706967345341801265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15937276471311563561200843 23905914706967345341801265)
              ·
                refine ⟨17929436030225509006350949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23905914706967345341801265 17929436030225509006350949)
                ·
                  refine ⟨3361769255667282938690803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17929436030225509006350949 3361769255667282938690803)
                  ·
                    refine ⟨5042653883500924408036205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3361769255667282938690803 5042653883500924408036205)
                    ·
                      refine ⟨1890995206312846653013577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5042653883500924408036205 1890995206312846653013577)
                      ·
                        rfl

theorem cell23_3682700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_3682700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682700 prefixEnd_3682700 := by exact prefixLift 3682700
  have htrace : WordTrace (prefixWord ++ tailWord_3682700) baseStart_3682700 baseEnd_3682700 := by
    simpa [prefixWord, tailWord_3682700, baseEnd_3682700] using wordTrace_append hprefix tailTrace_3682700
  have hstable : (prefixWord ++ tailWord_3682700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682700).length < 2 ^ (prefixWord ++ tailWord_3682700).sum := by decide
  have hdescent : baseEnd_3682700 < baseStart_3682700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682743 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 5]
def baseStart_3682743 : Nat := 118140960795 + 3682743 * 2 ^ 59
def prefixEnd_3682743 : Nat := 4983230072969 + 3 ^ 40 * 3682743 * 2
def baseEnd_3682743 : Nat := 1891017285980989984775879

theorem tailTrace_3682743 : CollatzResearch.WordTrace tailWord_3682743 prefixEnd_3682743 1891017285980989984775879 := by
  unfold tailWord_3682743
  simp only [CollatzResearch.WordTrace]
  refine ⟨134320672097058548275252883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89547114731372365516835255 134320672097058548275252883)
  ·
    refine ⟨201481008145587822412879325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134320672097058548275252883 201481008145587822412879325)
    ·
      refine ⟨75555378054595433404829747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201481008145587822412879325 75555378054595433404829747)
      ·
        refine ⟨113333067081893150107244621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75555378054595433404829747 113333067081893150107244621)
        ·
          refine ⟨42499900155709931290216733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113333067081893150107244621 42499900155709931290216733)
          ·
            refine ⟨15937462558391224233831275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42499900155709931290216733 15937462558391224233831275)
            ·
              refine ⟨23906193837586836350746913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15937462558391224233831275 23906193837586836350746913)
              ·
                refine ⟨17929645378190127263060185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23906193837586836350746913 17929645378190127263060185)
                ·
                  refine ⟨13447234033642595447295139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17929645378190127263060185 13447234033642595447295139)
                  ·
                    refine ⟨20170851050463893170942709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13447234033642595447295139 20170851050463893170942709)
                    ·
                      refine ⟨1891017285980989984775879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20170851050463893170942709 1891017285980989984775879)
                      ·
                        rfl

theorem cell23_3682743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_3682743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682743 prefixEnd_3682743 := by exact prefixLift 3682743
  have htrace : WordTrace (prefixWord ++ tailWord_3682743) baseStart_3682743 baseEnd_3682743 := by
    simpa [prefixWord, tailWord_3682743, baseEnd_3682743] using wordTrace_append hprefix tailTrace_3682743
  have hstable : (prefixWord ++ tailWord_3682743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682743).length < 2 ^ (prefixWord ++ tailWord_3682743).sum := by decide
  have hdescent : baseEnd_3682743 < baseStart_3682743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682800 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 2, 5, 2]
def baseStart_3682800 : Nat := 118140960795 + 3682800 * 2 ^ 59
def prefixEnd_3682800 : Nat := 4983230072969 + 3 ^ 40 * 3682800 * 2
def baseEnd_3682800 : Nat := 1891046554378296261763117

theorem tailTrace_3682800 : CollatzResearch.WordTrace tailWord_3682800 prefixEnd_3682800 1891046554378296261763117 := by
  unfold tailWord_3682800
  simp only [CollatzResearch.WordTrace]
  refine ⟨67161375528926023505038927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89548500705234698006718569 67161375528926023505038927)
  ·
    refine ⟨100742063293389035257558391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67161375528926023505038927 100742063293389035257558391)
    ·
      refine ⟨151113094940083552886337587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100742063293389035257558391 151113094940083552886337587)
      ·
        refine ⟨226669642410125329329506381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151113094940083552886337587 226669642410125329329506381)
        ·
          refine ⟨85001115903796998498564893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226669642410125329329506381 85001115903796998498564893)
          ·
            refine ⟨31875418463923874436961835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85001115903796998498564893 31875418463923874436961835)
            ·
              refine ⟨47813127695885811655442753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31875418463923874436961835 47813127695885811655442753)
              ·
                refine ⟨35859845771914358741582065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47813127695885811655442753 35859845771914358741582065)
                ·
                  refine ⟨26894884328935769056186549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35859845771914358741582065 26894884328935769056186549)
                  ·
                    refine ⟨2521395405837728349017489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26894884328935769056186549 2521395405837728349017489)
                    ·
                      refine ⟨1891046554378296261763117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2521395405837728349017489 1891046554378296261763117)
                      ·
                        rfl

theorem cell23_3682800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 2, 5, 2].length) (baseStart_3682800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682800 prefixEnd_3682800 := by exact prefixLift 3682800
  have htrace : WordTrace (prefixWord ++ tailWord_3682800) baseStart_3682800 baseEnd_3682800 := by
    simpa [prefixWord, tailWord_3682800, baseEnd_3682800] using wordTrace_append hprefix tailTrace_3682800
  have hstable : (prefixWord ++ tailWord_3682800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682800).length < 2 ^ (prefixWord ++ tailWord_3682800).sum := by decide
  have hdescent : baseEnd_3682800 < baseStart_3682800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682874 : List Nat := [3, 1, 1, 1, 3, 3, 3, 3, 1, 4]
def baseStart_3682874 : Nat := 118140960795 + 3682874 * 2 ^ 59
def prefixEnd_3682874 : Nat := 4983230072969 + 3 ^ 40 * 3682874 * 2
def baseEnd_3682874 : Nat := 630361517315576324079259

theorem tailTrace_3682874 : CollatzResearch.WordTrace tailWord_3682874 prefixEnd_3682874 630361517315576324079259 := by
  unfold tailWord_3682874
  simp only [CollatzResearch.WordTrace]
  refine ⟨33581362514895989412067919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89550300039722638432181117 33581362514895989412067919)
  ·
    refine ⟨50372043772343984118101879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33581362514895989412067919 50372043772343984118101879)
    ·
      refine ⟨75558065658515976177152819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50372043772343984118101879 75558065658515976177152819)
      ·
        refine ⟨113337098487773964265729229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75558065658515976177152819 113337098487773964265729229)
        ·
          refine ⟨42501411932915236599648461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113337098487773964265729229 42501411932915236599648461)
          ·
            refine ⟨15938029474843213724868173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42501411932915236599648461 15938029474843213724868173)
            ·
              refine ⟨5976761053066205146825565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15938029474843213724868173 5976761053066205146825565)
              ·
                refine ⟨2241285394899826930059587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5976761053066205146825565 2241285394899826930059587)
                ·
                  refine ⟨3361928092349740395089381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2241285394899826930059587 3361928092349740395089381)
                  ·
                    refine ⟨630361517315576324079259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3361928092349740395089381 630361517315576324079259)
                    ·
                      rfl

theorem cell23_3682874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_3682874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682874 prefixEnd_3682874 := by exact prefixLift 3682874
  have htrace : WordTrace (prefixWord ++ tailWord_3682874) baseStart_3682874 baseEnd_3682874 := by
    simpa [prefixWord, tailWord_3682874, baseEnd_3682874] using wordTrace_append hprefix tailTrace_3682874
  have hstable : (prefixWord ++ tailWord_3682874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682874).length < 2 ^ (prefixWord ++ tailWord_3682874).sum := by decide
  have hdescent : baseEnd_3682874 < baseStart_3682874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682917 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 3, 5]
def baseStart_3682917 : Nat := 118140960795 + 3682917 * 2 ^ 59
def prefixEnd_3682917 : Nat := 4983230072969 + 3 ^ 40 * 3682917 * 2
def baseEnd_3682917 : Nat := 630368877204957434666693

theorem tailTrace_3682917 : CollatzResearch.WordTrace tailWord_3682917 prefixEnd_3682917 630368877204957434666693 := by
  unfold tailWord_3682917
  simp only [CollatzResearch.WordTrace]
  refine ⟨134327018398428175992087005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89551345598952117328058003 134327018398428175992087005)
  ·
    refine ⟨50372631899410565997032627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134327018398428175992087005 50372631899410565997032627)
    ·
      refine ⟨75558947849115848995548941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50372631899410565997032627 75558947849115848995548941)
      ·
        refine ⟨28334605443418443373330853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75558947849115848995548941 28334605443418443373330853)
        ·
          refine ⟨5312738520640958132499535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28334605443418443373330853 5312738520640958132499535)
          ·
            refine ⟨7969107780961437198749303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5312738520640958132499535 7969107780961437198749303)
            ·
              refine ⟨11953661671442155798123955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7969107780961437198749303 11953661671442155798123955)
              ·
                refine ⟨17930492507163233697185933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11953661671442155798123955 17930492507163233697185933)
                ·
                  refine ⟨6723934690186212636444725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17930492507163233697185933 6723934690186212636444725)
                  ·
                    refine ⟨630368877204957434666693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6723934690186212636444725 630368877204957434666693)
                    ·
                      rfl

theorem cell23_3682917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_3682917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682917 prefixEnd_3682917 := by exact prefixLift 3682917
  have htrace : WordTrace (prefixWord ++ tailWord_3682917) baseStart_3682917 baseEnd_3682917 := by
    simpa [prefixWord, tailWord_3682917, baseEnd_3682917] using wordTrace_append hprefix tailTrace_3682917
  have hstable : (prefixWord ++ tailWord_3682917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682917).length < 2 ^ (prefixWord ++ tailWord_3682917).sum := by decide
  have hdescent : baseEnd_3682917 < baseStart_3682917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682947 : List Nat := [1, 1, 1, 3, 3, 1, 3, 4, 2, 4]
def baseStart_3682947 : Nat := 118140960795 + 3682947 * 2 ^ 59
def prefixEnd_3682947 : Nat := 4983230072969 + 3 ^ 40 * 3682947 * 2
def baseEnd_3682947 : Nat := 630374012011502395541647

theorem tailTrace_3682947 : CollatzResearch.WordTrace tailWord_3682947 prefixEnd_3682947 630374012011502395541647 := by
  unfold tailWord_3682947
  simp only [CollatzResearch.WordTrace]
  refine ⟨134328112588319491115679095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89552075058879660743786063 134328112588319491115679095)
  ·
    refine ⟨201492168882479236673518643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134328112588319491115679095 201492168882479236673518643)
    ·
      refine ⟨302238253323718855010277965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201492168882479236673518643 302238253323718855010277965)
      ·
        refine ⟨113339344996394570628854237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302238253323718855010277965 113339344996394570628854237)
        ·
          refine ⟨42502254373647963985820339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113339344996394570628854237 42502254373647963985820339)
          ·
            refine ⟨63753381560471945978730509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42502254373647963985820339 63753381560471945978730509)
            ·
              refine ⟨23907518085176979742023941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63753381560471945978730509 23907518085176979742023941)
              ·
                refine ⟨4482659640970683701629489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23907518085176979742023941 4482659640970683701629489)
                ·
                  refine ⟨3361994730728012776222117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4482659640970683701629489 3361994730728012776222117)
                  ·
                    refine ⟨630374012011502395541647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3361994730728012776222117 630374012011502395541647)
                    ·
                      rfl

theorem cell23_3682947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 4].length) (baseStart_3682947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682947 prefixEnd_3682947 := by exact prefixLift 3682947
  have htrace : WordTrace (prefixWord ++ tailWord_3682947) baseStart_3682947 baseEnd_3682947 := by
    simpa [prefixWord, tailWord_3682947, baseEnd_3682947] using wordTrace_append hprefix tailTrace_3682947
  have hstable : (prefixWord ++ tailWord_3682947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682947).length < 2 ^ (prefixWord ++ tailWord_3682947).sum := by decide
  have hdescent : baseEnd_3682947 < baseStart_3682947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682948 : List Nat := [2, 3, 2, 1, 3, 1, 4, 2, 1, 1, 3]
def baseStart_3682948 : Nat := 118140960795 + 3682948 * 2 ^ 59
def prefixEnd_3682948 : Nat := 4983230072969 + 3 ^ 40 * 3682948 * 2
def baseEnd_3682948 : Nat := 1891122549515161682712437

theorem tailTrace_3682948 : CollatzResearch.WordTrace tailWord_3682948 prefixEnd_3682948 1891122549515161682712437 := by
  unfold tailWord_3682948
  simp only [CollatzResearch.WordTrace]
  refine ⟨67164074530657934143232749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89552099374210578857643665 67164074530657934143232749)
  ·
    refine ⟨25186527948996725303712281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67164074530657934143232749 25186527948996725303712281)
    ·
      refine ⟨18889895961747543977784211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25186527948996725303712281 18889895961747543977784211)
      ·
        refine ⟨28334843942621315966676317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18889895961747543977784211 28334843942621315966676317)
        ·
          refine ⟨10625566478482993487503619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28334843942621315966676317 10625566478482993487503619)
          ·
            refine ⟨15938349717724490231255429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10625566478482993487503619 15938349717724490231255429)
            ·
              refine ⟨2988440572073341918360393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15938349717724490231255429 2988440572073341918360393)
              ·
                refine ⟨2241330429055006438770295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2988440572073341918360393 2241330429055006438770295)
                ·
                  refine ⟨3361995643582509658155443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2241330429055006438770295 3361995643582509658155443)
                  ·
                    refine ⟨5042993465373764487233165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3361995643582509658155443 5042993465373764487233165)
                    ·
                      refine ⟨1891122549515161682712437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5042993465373764487233165 1891122549515161682712437)
                      ·
                        rfl

theorem cell23_3682948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_3682948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682948 prefixEnd_3682948 := by exact prefixLift 3682948
  have htrace : WordTrace (prefixWord ++ tailWord_3682948) baseStart_3682948 baseEnd_3682948 := by
    simpa [prefixWord, tailWord_3682948, baseEnd_3682948] using wordTrace_append hprefix tailTrace_3682948
  have hstable : (prefixWord ++ tailWord_3682948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682948).length < 2 ^ (prefixWord ++ tailWord_3682948).sum := by decide
  have hdescent : baseEnd_3682948 < baseStart_3682948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682964 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_3682964 : Nat := 118140960795 + 3682964 * 2 ^ 59
def prefixEnd_3682964 : Nat := 4983230072969 + 3 ^ 40 * 3682964 * 2
def baseEnd_3682964 : Nat := 630376921735211206704121

theorem tailTrace_3682964 : CollatzResearch.WordTrace tailWord_3682964 prefixEnd_3682964 630376921735211206704121 := by
  unfold tailWord_3682964
  simp only [CollatzResearch.WordTrace]
  refine ⟨67164366314628951509523973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89552488419505268679365297 67164366314628951509523973)
  ·
    refine ⟨12593318683992928408035745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67164366314628951509523973 12593318683992928408035745)
    ·
      refine ⟨9444989012994696306026809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12593318683992928408035745 9444989012994696306026809)
      ·
        refine ⟨7083741759746022229520107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9444989012994696306026809 7083741759746022229520107)
        ·
          refine ⟨10625612639619033344280161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7083741759746022229520107 10625612639619033344280161)
          ·
            refine ⟨7969209479714275008210121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10625612639619033344280161 7969209479714275008210121)
            ·
              refine ⟨5976907109785706256157591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7969209479714275008210121 5976907109785706256157591)
              ·
                refine ⟨8965360664678559384236387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5976907109785706256157591 8965360664678559384236387)
                ·
                  refine ⟨13448040997017839076354581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8965360664678559384236387 13448040997017839076354581)
                  ·
                    refine ⟨630376921735211206704121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13448040997017839076354581 630376921735211206704121)
                    ·
                      rfl

theorem cell23_3682964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_3682964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682964 prefixEnd_3682964 := by exact prefixLift 3682964
  have htrace : WordTrace (prefixWord ++ tailWord_3682964) baseStart_3682964 baseEnd_3682964 := by
    simpa [prefixWord, tailWord_3682964, baseEnd_3682964] using wordTrace_append hprefix tailTrace_3682964
  have hstable : (prefixWord ++ tailWord_3682964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682964).length < 2 ^ (prefixWord ++ tailWord_3682964).sum := by decide
  have hdescent : baseEnd_3682964 < baseStart_3682964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682967 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 4]
def baseStart_3682967 : Nat := 118140960795 + 3682967 * 2 ^ 59
def prefixEnd_3682967 : Nat := 4983230072969 + 3 ^ 40 * 3682967 * 2
def baseEnd_3682967 : Nat := 1891132305647597108374849

theorem tailTrace_3682967 : CollatzResearch.WordTrace tailWord_3682967 prefixEnd_3682967 1891132305647597108374849 := by
  unfold tailWord_3682967
  simp only [CollatzResearch.WordTrace]
  refine ⟨134328842048247034531407155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89552561365498023020938103 134328842048247034531407155)
  ·
    refine ⟨201493263072370551797110733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134328842048247034531407155 201493263072370551797110733)
    ·
      refine ⟨75559973652138956923916525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201493263072370551797110733 75559973652138956923916525)
      ·
        refine ⟨28334990119552108846468697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75559973652138956923916525 28334990119552108846468697)
        ·
          refine ⟨21251242589664081634851523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28334990119552108846468697 21251242589664081634851523)
          ·
            refine ⟨31876863884496122452277285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21251242589664081634851523 31876863884496122452277285)
            ·
              refine ⟨5976911978343022959801991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31876863884496122452277285 5976911978343022959801991)
              ·
                refine ⟨8965367967514534439702987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5976911978343022959801991 8965367967514534439702987)
                ·
                  refine ⟨13448051951271801659554481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8965367967514534439702987 13448051951271801659554481)
                  ·
                    refine ⟨10086038963453851244665861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13448051951271801659554481 10086038963453851244665861)
                    ·
                      refine ⟨1891132305647597108374849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10086038963453851244665861 1891132305647597108374849)
                      ·
                        rfl

theorem cell23_3682967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_3682967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682967 prefixEnd_3682967 := by exact prefixLift 3682967
  have htrace : WordTrace (prefixWord ++ tailWord_3682967) baseStart_3682967 baseEnd_3682967 := by
    simpa [prefixWord, tailWord_3682967, baseEnd_3682967] using wordTrace_append hprefix tailTrace_3682967
  have hstable : (prefixWord ++ tailWord_3682967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682967).length < 2 ^ (prefixWord ++ tailWord_3682967).sum := by decide
  have hdescent : baseEnd_3682967 < baseStart_3682967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682974 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_3682974 : Nat := 118140960795 + 3682974 * 2 ^ 59
def prefixEnd_3682974 : Nat := 4983230072969 + 3 ^ 40 * 3682974 * 2
def baseEnd_3682974 : Nat := 1891135900012178580987317

theorem tailTrace_3682974 : CollatzResearch.WordTrace tailWord_3682974 prefixEnd_3682974 1891135900012178580987317 := by
  unfold tailWord_3682974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16791137169902709340863997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89552731572814449817941317 16791137169902709340863997)
  ·
    refine ⟨6296676438713516002823999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16791137169902709340863997 6296676438713516002823999)
    ·
      refine ⟨9445014658070274004235999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6296676438713516002823999 9445014658070274004235999)
      ·
        refine ⟨14167521987105411006353999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9445014658070274004235999 14167521987105411006353999)
        ·
          refine ⟨21251282980658116509530999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14167521987105411006353999 21251282980658116509530999)
          ·
            refine ⟨31876924470987174764296499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21251282980658116509530999 31876924470987174764296499)
            ·
              refine ⟨47815386706480762146444749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31876924470987174764296499 47815386706480762146444749)
              ·
                refine ⟨17930770014930285804916781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47815386706480762146444749 17930770014930285804916781)
                ·
                  refine ⟨6724038755598857176843793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17930770014930285804916781 6724038755598857176843793)
                  ·
                    refine ⟨5043029066699142882632845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6724038755598857176843793 5043029066699142882632845)
                    ·
                      refine ⟨1891135900012178580987317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5043029066699142882632845 1891135900012178580987317)
                      ·
                        rfl

theorem cell23_3682974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_3682974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682974 prefixEnd_3682974 := by exact prefixLift 3682974
  have htrace : WordTrace (prefixWord ++ tailWord_3682974) baseStart_3682974 baseEnd_3682974 := by
    simpa [prefixWord, tailWord_3682974, baseEnd_3682974] using wordTrace_append hprefix tailTrace_3682974
  have hstable : (prefixWord ++ tailWord_3682974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682974).length < 2 ^ (prefixWord ++ tailWord_3682974).sum := by decide
  have hdescent : baseEnd_3682974 < baseStart_3682974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3682991 : List Nat := [1, 1, 2, 1, 2, 7, 2, 1, 1, 2, 3]
def baseStart_3682991 : Nat := 118140960795 + 3682991 * 2 ^ 59
def prefixEnd_3682991 : Nat := 4983230072969 + 3 ^ 40 * 3682991 * 2
def baseEnd_3682991 : Nat := 1891144629183305014474739

theorem tailTrace_3682991 : CollatzResearch.WordTrace tailWord_3682991 prefixEnd_3682991 1891144629183305014474739 := by
  unfold tailWord_3682991
  simp only [CollatzResearch.WordTrace]
  refine ⟨134329717400160086630280827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89553144933440057753520551 134329717400160086630280827)
  ·
    refine ⟨201494576100240129945421241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134329717400160086630280827 201494576100240129945421241)
    ·
      refine ⟨151120932075180097459065931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201494576100240129945421241 151120932075180097459065931)
      ·
        refine ⟨226681398112770146188598897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151120932075180097459065931 226681398112770146188598897)
        ·
          refine ⟨170011048584577609641449173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226681398112770146188598897 170011048584577609641449173)
          ·
            refine ⟨3984633951201037725971465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 170011048584577609641449173 3984633951201037725971465)
            ·
              refine ⟨2988475463400778294478599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3984633951201037725971465 2988475463400778294478599)
              ·
                refine ⟨4482713195101167441717899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2988475463400778294478599 4482713195101167441717899)
                ·
                  refine ⟨6724069792651751162576849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4482713195101167441717899 6724069792651751162576849)
                  ·
                    refine ⟨5043052344488813371932637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6724069792651751162576849 5043052344488813371932637)
                    ·
                      refine ⟨1891144629183305014474739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5043052344488813371932637 1891144629183305014474739)
                      ·
                        rfl

theorem cell23_3682991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 1, 2, 3].length) (baseStart_3682991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3682991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3682991 prefixEnd_3682991 := by exact prefixLift 3682991
  have htrace : WordTrace (prefixWord ++ tailWord_3682991) baseStart_3682991 baseEnd_3682991 := by
    simpa [prefixWord, tailWord_3682991, baseEnd_3682991] using wordTrace_append hprefix tailTrace_3682991
  have hstable : (prefixWord ++ tailWord_3682991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3682991).length < 2 ^ (prefixWord ++ tailWord_3682991).sum := by decide
  have hdescent : baseEnd_3682991 < baseStart_3682991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3682991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683004 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 4, 1, 3]
def baseStart_3683004 : Nat := 118140960795 + 3683004 * 2 ^ 59
def prefixEnd_3683004 : Nat := 4983230072969 + 3 ^ 40 * 3683004 * 2
def baseEnd_3683004 : Nat := 1891151304431813463612179

theorem tailTrace_3683004 : CollatzResearch.WordTrace tailWord_3683004 prefixEnd_3683004 1891151304431813463612179 := by
  unfold tailWord_3683004
  simp only [CollatzResearch.WordTrace]
  refine ⟨67165095774556494925252033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89553461032741993233669377 67165095774556494925252033)
  ·
    refine ⟨50373821830917371193939025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67165095774556494925252033 50373821830917371193939025)
    ·
      refine ⟨37780366373188028395454269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50373821830917371193939025 37780366373188028395454269)
      ·
        refine ⟨14167637389945510648295351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37780366373188028395454269 14167637389945510648295351)
        ·
          refine ⟨21251456084918265972443027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14167637389945510648295351 21251456084918265972443027)
          ·
            refine ⟨31877184127377398958664541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21251456084918265972443027 31877184127377398958664541)
            ·
              refine ⟨11953944047766524609499203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31877184127377398958664541 11953944047766524609499203)
              ·
                refine ⟨17930916071649786914248805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11953944047766524609499203 17930916071649786914248805)
                ·
                  refine ⟨3362046763434335046421651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17930916071649786914248805 3362046763434335046421651)
                  ·
                    refine ⟨5043070145151502569632477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3362046763434335046421651 5043070145151502569632477)
                    ·
                      refine ⟨1891151304431813463612179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5043070145151502569632477 1891151304431813463612179)
                      ·
                        rfl

theorem cell23_3683004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_3683004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683004 prefixEnd_3683004 := by exact prefixLift 3683004
  have htrace : WordTrace (prefixWord ++ tailWord_3683004) baseStart_3683004 baseEnd_3683004 := by
    simpa [prefixWord, tailWord_3683004, baseEnd_3683004] using wordTrace_append hprefix tailTrace_3683004
  have hstable : (prefixWord ++ tailWord_3683004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683004).length < 2 ^ (prefixWord ++ tailWord_3683004).sum := by decide
  have hdescent : baseEnd_3683004 < baseStart_3683004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683031 : List Nat := [1, 1, 3, 2, 1, 5, 2, 2, 1, 3, 2]
def baseStart_3683031 : Nat := 118140960795 + 3683031 * 2 ^ 59
def prefixEnd_3683031 : Nat := 4983230072969 + 3 ^ 40 * 3683031 * 2
def baseEnd_3683031 : Nat := 1891165168409484857974555

theorem tailTrace_3683031 : CollatzResearch.WordTrace tailWord_3683031 prefixEnd_3683031 1891165168409484857974555 := by
  unfold tailWord_3683031
  simp only [CollatzResearch.WordTrace]
  refine ⟨134331176320015173461736947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89554117546676782307824631 134331176320015173461736947)
  ·
    refine ⟨201496764480022760192605421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134331176320015173461736947 201496764480022760192605421)
    ·
      refine ⟨75561286680008535072227033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201496764480022760192605421 75561286680008535072227033)
      ·
        refine ⟨56670965010006401304170275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75561286680008535072227033 56670965010006401304170275)
        ·
          refine ⟨85006447515009601956255413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56670965010006401304170275 85006447515009601956255413)
          ·
            refine ⟨7969354454532150183398945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85006447515009601956255413 7969354454532150183398945)
            ·
              refine ⟨5977015840899112637549209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7969354454532150183398945 5977015840899112637549209)
              ·
                refine ⟨4482761880674334478161907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5977015840899112637549209 4482761880674334478161907)
                ·
                  refine ⟨6724142821011501717242861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4482761880674334478161907 6724142821011501717242861)
                  ·
                    refine ⟨2521553557879313143966073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6724142821011501717242861 2521553557879313143966073)
                    ·
                      refine ⟨1891165168409484857974555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2521553557879313143966073 1891165168409484857974555)
                      ·
                        rfl

theorem cell23_3683031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_3683031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683031 prefixEnd_3683031 := by exact prefixLift 3683031
  have htrace : WordTrace (prefixWord ++ tailWord_3683031) baseStart_3683031 baseEnd_3683031 := by
    simpa [prefixWord, tailWord_3683031, baseEnd_3683031] using wordTrace_append hprefix tailTrace_3683031
  have hstable : (prefixWord ++ tailWord_3683031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683031).length < 2 ^ (prefixWord ++ tailWord_3683031).sum := by decide
  have hdescent : baseEnd_3683031 < baseStart_3683031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683077 : List Nat := [1, 3, 1, 1, 2, 1, 1, 5, 2, 3, 3]
def baseStart_3683077 : Nat := 118140960795 + 3683077 * 2 ^ 59
def prefixEnd_3683077 : Nat := 4983230072969 + 3 ^ 40 * 3683077 * 2
def baseEnd_3683077 : Nat := 1891188788519591677999343

theorem tailTrace_3683077 : CollatzResearch.WordTrace tailWord_3683077 prefixEnd_3683077 1891188788519591677999343 := by
  unfold tailWord_3683077
  simp only [CollatzResearch.WordTrace]
  refine ⟨134332854077848523317911485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89555236051899015545274323 134332854077848523317911485)
  ·
    refine ⟨50374820279193196244216807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134332854077848523317911485 50374820279193196244216807)
    ·
      refine ⟨75562230418789794366325211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50374820279193196244216807 75562230418789794366325211)
      ·
        refine ⟨113343345628184691549487817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75562230418789794366325211 113343345628184691549487817)
        ·
          refine ⟨85007509221138518662115863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113343345628184691549487817 85007509221138518662115863)
          ·
            refine ⟨127511263831707777993173795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85007509221138518662115863 127511263831707777993173795)
            ·
              refine ⟨191266895747561666989760693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127511263831707777993173795 191266895747561666989760693)
              ·
                refine ⟨17931271476333906280290065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 191266895747561666989760693 17931271476333906280290065)
                ·
                  refine ⟨13448453607250429710217549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17931271476333906280290065 13448453607250429710217549)
                  ·
                    refine ⟨5043170102718911141331581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13448453607250429710217549 5043170102718911141331581)
                    ·
                      refine ⟨1891188788519591677999343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5043170102718911141331581 1891188788519591677999343)
                      ·
                        rfl

theorem cell23_3683077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_3683077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683077 prefixEnd_3683077 := by exact prefixLift 3683077
  have htrace : WordTrace (prefixWord ++ tailWord_3683077) baseStart_3683077 baseEnd_3683077 := by
    simpa [prefixWord, tailWord_3683077, baseEnd_3683077] using wordTrace_append hprefix tailTrace_3683077
  have hstable : (prefixWord ++ tailWord_3683077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683077).length < 2 ^ (prefixWord ++ tailWord_3683077).sum := by decide
  have hdescent : baseEnd_3683077 < baseStart_3683077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683118 : List Nat := [4, 1, 3, 2, 1, 1, 4, 2, 5]
def baseStart_3683118 : Nat := 118140960795 + 3683118 * 2 ^ 59
def prefixEnd_3683118 : Nat := 4983230072969 + 3 ^ 40 * 3683118 * 2
def baseEnd_3683118 : Nat := 210134426802936224176295

theorem tailTrace_3683118 : CollatzResearch.WordTrace tailWord_3683118 prefixEnd_3683118 210134426802936224176295 := by
  unfold tailWord_3683118
  simp only [CollatzResearch.WordTrace]
  refine ⟨16791793683837498415019251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89556232980466658213436005 16791793683837498415019251)
  ·
    refine ⟨25187690525756247622528877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16791793683837498415019251 25187690525756247622528877)
    ·
      refine ⟨9445383947158592858448329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25187690525756247622528877 9445383947158592858448329)
      ·
        refine ⟨7084037960368944643836247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9445383947158592858448329 7084037960368944643836247)
        ·
          refine ⟨10626056940553416965754371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7084037960368944643836247 10626056940553416965754371)
          ·
            refine ⟨15939085410830125448631557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10626056940553416965754371 15939085410830125448631557)
            ·
              refine ⟨2988578514530648521618417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15939085410830125448631557 2988578514530648521618417)
              ·
                refine ⟨2241433885897986391213813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2988578514530648521618417 2241433885897986391213813)
                ·
                  refine ⟨210134426802936224176295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2241433885897986391213813 210134426802936224176295)
                  ·
                    rfl

theorem cell23_3683118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_3683118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683118 prefixEnd_3683118 := by exact prefixLift 3683118
  have htrace : WordTrace (prefixWord ++ tailWord_3683118) baseStart_3683118 baseEnd_3683118 := by
    simpa [prefixWord, tailWord_3683118, baseEnd_3683118] using wordTrace_append hprefix tailTrace_3683118
  have hstable : (prefixWord ++ tailWord_3683118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683118).length < 2 ^ (prefixWord ++ tailWord_3683118).sum := by decide
  have hdescent : baseEnd_3683118 < baseStart_3683118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683144 : List Nat := [2, 1, 3, 1, 1, 3, 3, 2, 3, 4]
def baseStart_3683144 : Nat := 118140960795 + 3683144 * 2 ^ 59
def prefixEnd_3683144 : Nat := 4983230072969 + 3 ^ 40 * 3683144 * 2
def baseEnd_3683144 : Nat := 630407730574480971953845

theorem tailTrace_3683144 : CollatzResearch.WordTrace tailWord_3683144 prefixEnd_3683144 630407730574480971953845 := by
  unfold tailWord_3683144
  simp only [CollatzResearch.WordTrace]
  refine ⟨67167648884302896880300243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89556865179070529173733657 67167648884302896880300243)
  ·
    refine ⟨100751473326454345320450365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67167648884302896880300243 100751473326454345320450365)
    ·
      refine ⟨37781802497420379495168887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100751473326454345320450365 37781802497420379495168887)
      ·
        refine ⟨56672703746130569242753331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37781802497420379495168887 56672703746130569242753331)
        ·
          refine ⟨85009055619195853864129997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56672703746130569242753331 85009055619195853864129997)
          ·
            refine ⟨31878395857198445199048749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85009055619195853864129997 31878395857198445199048749)
            ·
              refine ⟨11954398446449416949643281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31878395857198445199048749 11954398446449416949643281)
              ·
                refine ⟨8965798834837062712232461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11954398446449416949643281 8965798834837062712232461)
                ·
                  refine ⟨3362174563063898517087173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8965798834837062712232461 3362174563063898517087173)
                  ·
                    refine ⟨630407730574480971953845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3362174563063898517087173 630407730574480971953845)
                    ·
                      rfl

theorem cell23_3683144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_3683144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683144 prefixEnd_3683144 := by exact prefixLift 3683144
  have htrace : WordTrace (prefixWord ++ tailWord_3683144) baseStart_3683144 baseEnd_3683144 := by
    simpa [prefixWord, tailWord_3683144, baseEnd_3683144] using wordTrace_append hprefix tailTrace_3683144
  have hstable : (prefixWord ++ tailWord_3683144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683144).length < 2 ^ (prefixWord ++ tailWord_3683144).sum := by decide
  have hdescent : baseEnd_3683144 < baseStart_3683144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683154 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_3683154 : Nat := 118140960795 + 3683154 * 2 ^ 59
def prefixEnd_3683154 : Nat := 4983230072969 + 3 ^ 40 * 3683154 * 2
def baseEnd_3683154 : Nat := 1891228326529987876736489

theorem tailTrace_3683154 : CollatzResearch.WordTrace tailWord_3683154 prefixEnd_3683154 1891228326529987876736489 := by
  unfold tailWord_3683154
  simp only [CollatzResearch.WordTrace]
  refine ⟨33583915624642391367116129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89557108332379710312309677 33583915624642391367116129)
  ·
    refine ⟨25187936718481793525337097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33583915624642391367116129 25187936718481793525337097)
    ·
      refine ⟨18890952538861345144002823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25187936718481793525337097 18890952538861345144002823)
      ·
        refine ⟨28336428808292017716004235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18890952538861345144002823 28336428808292017716004235)
        ·
          refine ⟨42504643212438026574006353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28336428808292017716004235 42504643212438026574006353)
          ·
            refine ⟨31878482409328519930504765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42504643212438026574006353 31878482409328519930504765)
            ·
              refine ⟨11954430903498194973939287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31878482409328519930504765 11954430903498194973939287)
              ·
                refine ⟨17931646355247292460908931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11954430903498194973939287 17931646355247292460908931)
                ·
                  refine ⟨26897469532870938691363397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17931646355247292460908931 26897469532870938691363397)
                  ·
                    refine ⟨5043275537413301004630637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26897469532870938691363397 5043275537413301004630637)
                    ·
                      refine ⟨1891228326529987876736489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5043275537413301004630637 1891228326529987876736489)
                      ·
                        rfl

theorem cell23_3683154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_3683154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683154 prefixEnd_3683154 := by exact prefixLift 3683154
  have htrace : WordTrace (prefixWord ++ tailWord_3683154) baseStart_3683154 baseEnd_3683154 := by
    simpa [prefixWord, tailWord_3683154, baseEnd_3683154] using wordTrace_append hprefix tailTrace_3683154
  have hstable : (prefixWord ++ tailWord_3683154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683154).length < 2 ^ (prefixWord ++ tailWord_3683154).sum := by decide
  have hdescent : baseEnd_3683154 < baseStart_3683154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683157 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 8]
def baseStart_3683157 : Nat := 118140960795 + 3683157 * 2 ^ 59
def prefixEnd_3683157 : Nat := 4983230072969 + 3 ^ 40 * 3683157 * 2
def baseEnd_3683157 : Nat := 210136651885772373888775

theorem tailTrace_3683157 : CollatzResearch.WordTrace tailWord_3683157 prefixEnd_3683157 210136651885772373888775 := by
  unfold tailWord_3683157
  simp only [CollatzResearch.WordTrace]
  refine ⟨134335771917558696980823725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89557181278372464653882483 134335771917558696980823725)
  ·
    refine ⟨50375914469084511367808897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134335771917558696980823725 50375914469084511367808897)
    ·
      refine ⟨37781935851813383525856673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50375914469084511367808897 37781935851813383525856673)
      ·
        refine ⟨28336451888860037644392505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37781935851813383525856673 28336451888860037644392505)
        ·
          refine ⟨21252338916645028233294379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28336451888860037644392505 21252338916645028233294379)
          ·
            refine ⟨31878508374967542349941569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21252338916645028233294379 31878508374967542349941569)
            ·
              refine ⟨23908881281225656762456177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31878508374967542349941569 23908881281225656762456177)
              ·
                refine ⟨17931660960919242571842133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23908881281225656762456177 17931660960919242571842133)
                ·
                  refine ⟨210136651885772373888775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17931660960919242571842133 210136651885772373888775)
                  ·
                    rfl

theorem cell23_3683157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 8].length) (baseStart_3683157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683157 prefixEnd_3683157 := by exact prefixLift 3683157
  have htrace : WordTrace (prefixWord ++ tailWord_3683157) baseStart_3683157 baseEnd_3683157 := by
    simpa [prefixWord, tailWord_3683157, baseEnd_3683157] using wordTrace_append hprefix tailTrace_3683157
  have hstable : (prefixWord ++ tailWord_3683157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683157).length < 2 ^ (prefixWord ++ tailWord_3683157).sum := by decide
  have hdescent : baseEnd_3683157 < baseStart_3683157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683161 : List Nat := [1, 2, 1, 2, 2, 4, 1, 5, 1, 4]
def baseStart_3683161 : Nat := 118140960795 + 3683161 * 2 ^ 59
def prefixEnd_3683161 : Nat := 4983230072969 + 3 ^ 40 * 3683161 * 2
def baseEnd_3683161 : Nat := 630410640298189783116319

theorem tailTrace_3683161 : CollatzResearch.WordTrace tailWord_3683161 prefixEnd_3683161 630410640298189783116319 := by
  unfold tailWord_3683161
  simp only [CollatzResearch.WordTrace]
  refine ⟨134335917809544205663969337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89557278539696137109312891 134335917809544205663969337)
  ·
    refine ⟨100751938357158154247977003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134335917809544205663969337 100751938357158154247977003)
    ·
      refine ⟨151127907535737231371965505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100751938357158154247977003 151127907535737231371965505)
      ·
        refine ⟨113345930651802923528974129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151127907535737231371965505 113345930651802923528974129)
        ·
          refine ⟨85009447988852192646730597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113345930651802923528974129 85009447988852192646730597)
          ·
            refine ⟨15939271497909786121261987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85009447988852192646730597 15939271497909786121261987)
            ·
              refine ⟨23908907246864679181892981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15939271497909786121261987 23908907246864679181892981)
              ·
                refine ⟨2241460054393563673302467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23908907246864679181892981 2241460054393563673302467)
                ·
                  refine ⟨3362190081590345509953701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2241460054393563673302467 3362190081590345509953701)
                  ·
                    refine ⟨630410640298189783116319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3362190081590345509953701 630410640298189783116319)
                    ·
                      rfl

theorem cell23_3683161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 5, 1, 4].length) (baseStart_3683161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683161 prefixEnd_3683161 := by exact prefixLift 3683161
  have htrace : WordTrace (prefixWord ++ tailWord_3683161) baseStart_3683161 baseEnd_3683161 := by
    simpa [prefixWord, tailWord_3683161, baseEnd_3683161] using wordTrace_append hprefix tailTrace_3683161
  have hstable : (prefixWord ++ tailWord_3683161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683161).length < 2 ^ (prefixWord ++ tailWord_3683161).sum := by decide
  have hdescent : baseEnd_3683161 < baseStart_3683161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683164 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3683164 : Nat := 118140960795 + 3683164 * 2 ^ 59
def prefixEnd_3683164 : Nat := 4983230072969 + 3 ^ 40 * 3683164 * 2
def baseEnd_3683164 : Nat := 1891233461336532837611443

theorem tailTrace_3683164 : CollatzResearch.WordTrace tailWord_3683164 prefixEnd_3683164 1891233461336532837611443 := by
  unfold tailWord_3683164
  simp only [CollatzResearch.WordTrace]
  refine ⟨67168013614266668588164273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89557351485688891450885697 67168013614266668588164273)
  ·
    refine ⟨50376010210700001441123205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67168013614266668588164273 50376010210700001441123205)
    ·
      refine ⟨9445501914506250270210601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50376010210700001441123205 9445501914506250270210601)
      ·
        refine ⟨7084126435879687702657951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9445501914506250270210601 7084126435879687702657951)
        ·
          refine ⟨10626189653819531553986927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7084126435879687702657951 10626189653819531553986927)
          ·
            refine ⟨15939284480729297330980391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10626189653819531553986927 15939284480729297330980391)
            ·
              refine ⟨23908926721093945996470587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15939284480729297330980391 23908926721093945996470587)
              ·
                refine ⟨35863390081640918994705881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23908926721093945996470587 35863390081640918994705881)
                ·
                  refine ⟨26897542561230689246029411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35863390081640918994705881 26897542561230689246029411)
                  ·
                    refine ⟨40346313841846033869044117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26897542561230689246029411 40346313841846033869044117)
                    ·
                      refine ⟨1891233461336532837611443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40346313841846033869044117 1891233461336532837611443)
                      ·
                        rfl

theorem cell23_3683164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3683164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683164 prefixEnd_3683164 := by exact prefixLift 3683164
  have htrace : WordTrace (prefixWord ++ tailWord_3683164) baseStart_3683164 baseEnd_3683164 := by
    simpa [prefixWord, tailWord_3683164, baseEnd_3683164] using wordTrace_append hprefix tailTrace_3683164
  have hstable : (prefixWord ++ tailWord_3683164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683164).length < 2 ^ (prefixWord ++ tailWord_3683164).sum := by decide
  have hdescent : baseEnd_3683164 < baseStart_3683164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683187 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 5, 5]
def baseStart_3683187 : Nat := 118140960795 + 3683187 * 2 ^ 59
def prefixEnd_3683187 : Nat := 4983230072969 + 3 ^ 40 * 3683187 * 2
def baseEnd_3683187 : Nat := 630415090463862082541279

theorem tailTrace_3683187 : CollatzResearch.WordTrace tailWord_3683187 prefixEnd_3683187 630415090463862082541279 := by
  unfold tailWord_3683187
  simp only [CollatzResearch.WordTrace]
  refine ⟨134336866107450012104415815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89557910738300008069610543 134336866107450012104415815)
  ·
    refine ⟨201505299161175018156623723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134336866107450012104415815 201505299161175018156623723)
    ·
      refine ⟨302257948741762527234935585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201505299161175018156623723 302257948741762527234935585)
      ·
        refine ⟨226693461556321895426201689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302257948741762527234935585 226693461556321895426201689)
        ·
          refine ⟨170020096167241421569651267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226693461556321895426201689 170020096167241421569651267)
          ·
            refine ⟨255030144250862132354476901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170020096167241421569651267 255030144250862132354476901)
            ·
              refine ⟨47818152047036649816464419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255030144250862132354476901 47818152047036649816464419)
              ·
                refine ⟨71727228070554974724696629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47818152047036649816464419 71727228070554974724696629)
                ·
                  refine ⟨6724427631614528880440309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71727228070554974724696629 6724427631614528880440309)
                  ·
                    refine ⟨630415090463862082541279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6724427631614528880440309 630415090463862082541279)
                    ·
                      rfl

theorem cell23_3683187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 5].length) (baseStart_3683187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683187 prefixEnd_3683187 := by exact prefixLift 3683187
  have htrace : WordTrace (prefixWord ++ tailWord_3683187) baseStart_3683187 baseEnd_3683187 := by
    simpa [prefixWord, tailWord_3683187, baseEnd_3683187] using wordTrace_append hprefix tailTrace_3683187
  have hstable : (prefixWord ++ tailWord_3683187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683187).length < 2 ^ (prefixWord ++ tailWord_3683187).sum := by decide
  have hdescent : baseEnd_3683187 < baseStart_3683187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683197 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_3683197 : Nat := 118140960795 + 3683197 * 2 ^ 59
def prefixEnd_3683197 : Nat := 4983230072969 + 3 ^ 40 * 3683197 * 2
def baseEnd_3683197 : Nat := 1891250406198131208498791

theorem tailTrace_3683197 : CollatzResearch.WordTrace tailWord_3683197 prefixEnd_3683197 1891250406198131208498791 := by
  unfold tailWord_3683197
  simp only [CollatzResearch.WordTrace]
  refine ⟨134337230837413783812279845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89558153891609189208186563 134337230837413783812279845)
  ·
    refine ⟨25188230782015084464802471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134337230837413783812279845 25188230782015084464802471)
    ·
      refine ⟨37782346173022626697203707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25188230782015084464802471 37782346173022626697203707)
      ·
        refine ⟨56673519259533940045805561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37782346173022626697203707 56673519259533940045805561)
        ·
          refine ⟨42505139444650455034354171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56673519259533940045805561 42505139444650455034354171)
          ·
            refine ⟨63757709166975682551531257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42505139444650455034354171 63757709166975682551531257)
            ·
              refine ⟨47818281875231761913648443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63757709166975682551531257 47818281875231761913648443)
              ·
                refine ⟨71727422812847642870472665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47818281875231761913648443 71727422812847642870472665)
                ·
                  refine ⟨53795567109635732152854499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71727422812847642870472665 53795567109635732152854499)
                  ·
                    refine ⟨80693350664453598229281749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53795567109635732152854499 80693350664453598229281749)
                    ·
                      refine ⟨1891250406198131208498791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80693350664453598229281749 1891250406198131208498791)
                      ·
                        rfl

theorem cell23_3683197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_3683197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683197 prefixEnd_3683197 := by exact prefixLift 3683197
  have htrace : WordTrace (prefixWord ++ tailWord_3683197) baseStart_3683197 baseEnd_3683197 := by
    simpa [prefixWord, tailWord_3683197, baseEnd_3683197] using wordTrace_append hprefix tailTrace_3683197
  have hstable : (prefixWord ++ tailWord_3683197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683197).length < 2 ^ (prefixWord ++ tailWord_3683197).sum := by decide
  have hdescent : baseEnd_3683197 < baseStart_3683197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683217 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 3, 6]
def baseStart_3683217 : Nat := 118140960795 + 3683217 * 2 ^ 59
def prefixEnd_3683217 : Nat := 4983230072969 + 3 ^ 40 * 3683217 * 2
def baseEnd_3683217 : Nat := 630420225270407043416233

theorem tailTrace_3683217 : CollatzResearch.WordTrace tailWord_3683217 prefixEnd_3683217 630420225270407043416233 := by
  unfold tailWord_3683217
  simp only [CollatzResearch.WordTrace]
  refine ⟨134337960297341327228007905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89558640198227551485338603 134337960297341327228007905)
  ·
    refine ⟨100753470223005995421005929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134337960297341327228007905 100753470223005995421005929)
    ·
      refine ⟨75565102667254496565754447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100753470223005995421005929 75565102667254496565754447)
      ·
        refine ⟨113347654000881744848631671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75565102667254496565754447 113347654000881744848631671)
        ·
          refine ⟨170021481001322617272947507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113347654000881744848631671 170021481001322617272947507)
          ·
            refine ⟨255032221501983925909421261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170021481001322617272947507 255032221501983925909421261)
            ·
              refine ⟨95637083063243972216032973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255032221501983925909421261 95637083063243972216032973)
              ·
                refine ⟨35863906148716489581012365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95637083063243972216032973 35863906148716489581012365)
                ·
                  refine ⟨13448964805768683592879637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35863906148716489581012365 13448964805768683592879637)
                  ·
                    refine ⟨630420225270407043416233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13448964805768683592879637 630420225270407043416233)
                    ·
                      rfl

theorem cell23_3683217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_3683217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683217 prefixEnd_3683217 := by exact prefixLift 3683217
  have htrace : WordTrace (prefixWord ++ tailWord_3683217) baseStart_3683217 baseEnd_3683217 := by
    simpa [prefixWord, tailWord_3683217, baseEnd_3683217] using wordTrace_append hprefix tailTrace_3683217
  have hstable : (prefixWord ++ tailWord_3683217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683217).length < 2 ^ (prefixWord ++ tailWord_3683217).sum := by decide
  have hdescent : baseEnd_3683217 < baseStart_3683217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683244 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 3]
def baseStart_3683244 : Nat := 118140960795 + 3683244 * 2 ^ 59
def prefixEnd_3683244 : Nat := 4983230072969 + 3 ^ 40 * 3683244 * 2
def baseEnd_3683244 : Nat := 1891274539788892524611075

theorem tailTrace_3683244 : CollatzResearch.WordTrace tailWord_3683244 prefixEnd_3683244 1891274539788892524611075 := by
  unfold tailWord_3683244
  simp only [CollatzResearch.WordTrace]
  refine ⟨67169472534121755419620393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89559296712162340559493857 67169472534121755419620393)
  ·
    refine ⟨50377104400591316564715295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67169472534121755419620393 50377104400591316564715295)
    ·
      refine ⟨75565656600886974847072943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50377104400591316564715295 75565656600886974847072943)
      ·
        refine ⟨113348484901330462270609415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75565656600886974847072943 113348484901330462270609415)
        ·
          refine ⟨170022727351995693405914123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113348484901330462270609415 170022727351995693405914123)
          ·
            refine ⟨255034091027993540108871185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170022727351995693405914123 255034091027993540108871185)
            ·
              refine ⟨191275568270995155081653389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255034091027993540108871185 191275568270995155081653389)
              ·
                refine ⟨71728338101623183155620021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191275568270995155081653389 71728338101623183155620021)
                ·
                  refine ⟨6724531697027173420839377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71728338101623183155620021 6724531697027173420839377)
                  ·
                    refine ⟨5043398772770380065629533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6724531697027173420839377 5043398772770380065629533)
                    ·
                      refine ⟨1891274539788892524611075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5043398772770380065629533 1891274539788892524611075)
                      ·
                        rfl

theorem cell23_3683244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_3683244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683244 prefixEnd_3683244 := by exact prefixLift 3683244
  have htrace : WordTrace (prefixWord ++ tailWord_3683244) baseStart_3683244 baseEnd_3683244 := by
    simpa [prefixWord, tailWord_3683244, baseEnd_3683244] using wordTrace_append hprefix tailTrace_3683244
  have hstable : (prefixWord ++ tailWord_3683244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683244).length < 2 ^ (prefixWord ++ tailWord_3683244).sum := by decide
  have hdescent : baseEnd_3683244 < baseStart_3683244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683267 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 6]
def baseStart_3683267 : Nat := 118140960795 + 3683267 * 2 ^ 59
def prefixEnd_3683267 : Nat := 4983230072969 + 3 ^ 40 * 3683267 * 2
def baseEnd_3683267 : Nat := 1891286349843945934623469

theorem tailTrace_3683267 : CollatzResearch.WordTrace tailWord_3683267 prefixEnd_3683267 1891286349843945934623469 := by
  unfold tailWord_3683267
  simp only [CollatzResearch.WordTrace]
  refine ⟨134339783947160185767328055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89559855964773457178218703 134339783947160185767328055)
  ·
    refine ⟨201509675920740278650992083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134339783947160185767328055 201509675920740278650992083)
    ·
      refine ⟨302264513881110417976488125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201509675920740278650992083 302264513881110417976488125)
      ·
        refine ⟨113349192705416406741183047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302264513881110417976488125 113349192705416406741183047)
        ·
          refine ⟨170023789058124610111774571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113349192705416406741183047 170023789058124610111774571)
          ·
            refine ⟨255035683587186915167661857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170023789058124610111774571 255035683587186915167661857)
            ·
              refine ⟨191276762690390186375746393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255035683587186915167661857 191276762690390186375746393)
              ·
                refine ⟨143457572017792639781809795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191276762690390186375746393 143457572017792639781809795)
                ·
                  refine ⟨215186358026688959672714693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143457572017792639781809795 215186358026688959672714693)
                  ·
                    refine ⟨40347442130004179938634005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 215186358026688959672714693 40347442130004179938634005)
                    ·
                      refine ⟨1891286349843945934623469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40347442130004179938634005 1891286349843945934623469)
                      ·
                        rfl

theorem cell23_3683267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_3683267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683267 prefixEnd_3683267 := by exact prefixLift 3683267
  have htrace : WordTrace (prefixWord ++ tailWord_3683267) baseStart_3683267 baseEnd_3683267 := by
    simpa [prefixWord, tailWord_3683267, baseEnd_3683267] using wordTrace_append hprefix tailTrace_3683267
  have hstable : (prefixWord ++ tailWord_3683267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683267).length < 2 ^ (prefixWord ++ tailWord_3683267).sum := by decide
  have hdescent : baseEnd_3683267 < baseStart_3683267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683268 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 1, 6]
def baseStart_3683268 : Nat := 118140960795 + 3683268 * 2 ^ 59
def prefixEnd_3683268 : Nat := 4983230072969 + 3 ^ 40 * 3683268 * 2
def baseEnd_3683268 : Nat := 630428954441533476903655

theorem tailTrace_3683268 : CollatzResearch.WordTrace tailWord_3683268 prefixEnd_3683268 630428954441533476903655 := by
  unfold tailWord_3683268
  simp only [CollatzResearch.WordTrace]
  refine ⟨67169910210078281469057229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89559880280104375292076305 67169910210078281469057229)
  ·
    refine ⟨25188716328779355550896461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67169910210078281469057229 25188716328779355550896461)
    ·
      refine ⟨9445768623292258331586173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25188716328779355550896461 9445768623292258331586173)
      ·
        refine ⟨3542163233734596874344815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9445768623292258331586173 3542163233734596874344815)
        ·
          refine ⟨5313244850601895311517223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3542163233734596874344815 5313244850601895311517223)
          ·
            refine ⟨7969867275902842967275835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5313244850601895311517223 7969867275902842967275835)
            ·
              refine ⟨11954800913854264450913753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7969867275902842967275835 11954800913854264450913753)
              ·
                refine ⟨8966100685390698338185315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11954800913854264450913753 8966100685390698338185315)
                ·
                  refine ⟨13449151028086047507277973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8966100685390698338185315 13449151028086047507277973)
                  ·
                    refine ⟨630428954441533476903655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13449151028086047507277973 630428954441533476903655)
                    ·
                      rfl

theorem cell23_3683268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_3683268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683268 prefixEnd_3683268 := by exact prefixLift 3683268
  have htrace : WordTrace (prefixWord ++ tailWord_3683268) baseStart_3683268 baseEnd_3683268 := by
    simpa [prefixWord, tailWord_3683268, baseEnd_3683268] using wordTrace_append hprefix tailTrace_3683268
  have hstable : (prefixWord ++ tailWord_3683268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683268).length < 2 ^ (prefixWord ++ tailWord_3683268).sum := by decide
  have hdescent : baseEnd_3683268 < baseStart_3683268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683298 : List Nat := [3, 3, 3, 1, 1, 3, 1, 8]
def baseStart_3683298 : Nat := 118140960795 + 3683298 * 2 ^ 59
def prefixEnd_3683298 : Nat := 4983230072969 + 3 ^ 40 * 3683298 * 2
def baseEnd_3683298 : Nat := 70048232138675381975401

theorem tailTrace_3683298 : CollatzResearch.WordTrace tailWord_3683298 prefixEnd_3683298 70048232138675381975401 := by
  unfold tailWord_3683298
  simp only [CollatzResearch.WordTrace]
  refine ⟨33585228652511969515426637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89560609740031918707804365 33585228652511969515426637)
  ·
    refine ⟨12594460744691988568284989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33585228652511969515426637 12594460744691988568284989)
    ·
      refine ⟨4722922779259495713106871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12594460744691988568284989 4722922779259495713106871)
      ·
        refine ⟨7084384168889243569660307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4722922779259495713106871 7084384168889243569660307)
        ·
          refine ⟨10626576253333865354490461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7084384168889243569660307 10626576253333865354490461)
          ·
            refine ⟨3984966095000199507933923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10626576253333865354490461 3984966095000199507933923)
            ·
              refine ⟨5977449142500299261900885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3984966095000199507933923 5977449142500299261900885)
              ·
                refine ⟨70048232138675381975401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5977449142500299261900885 70048232138675381975401)
                ·
                  rfl

theorem cell23_3683298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 8].length) (baseStart_3683298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683298 prefixEnd_3683298 := by exact prefixLift 3683298
  have htrace : WordTrace (prefixWord ++ tailWord_3683298) baseStart_3683298 baseEnd_3683298 := by
    simpa [prefixWord, tailWord_3683298, baseEnd_3683298] using wordTrace_append hprefix tailTrace_3683298
  have hstable : (prefixWord ++ tailWord_3683298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683298).length < 2 ^ (prefixWord ++ tailWord_3683298).sum := by decide
  have hdescent : baseEnd_3683298 < baseStart_3683298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683361 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3683361 : Nat := 118140960795 + 3683361 * 2 ^ 59
def prefixEnd_3683361 : Nat := 4983230072969 + 3 ^ 40 * 3683361 * 2
def baseEnd_3683361 : Nat := 1891334617025468566848037

theorem tailTrace_3683361 : CollatzResearch.WordTrace tailWord_3683361 prefixEnd_3683361 1891334617025468566848037 := by
  unfold tailWord_3683361
  simp only [CollatzResearch.WordTrace]
  refine ⟨134343212408819639821249937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89562141605879759880833291 134343212408819639821249937)
  ·
    refine ⟨100757409306614729865937453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134343212408819639821249937 100757409306614729865937453)
    ·
      refine ⟨37784028489980523699726545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100757409306614729865937453 37784028489980523699726545)
      ·
        refine ⟨28338021367485392774794909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37784028489980523699726545 28338021367485392774794909)
        ·
          refine ⟨10626758012807022290548091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28338021367485392774794909 10626758012807022290548091)
          ·
            refine ⟨15940137019210533435822137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10626758012807022290548091 15940137019210533435822137)
            ·
              refine ⟨11955102764407900076866603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15940137019210533435822137 11955102764407900076866603)
              ·
                refine ⟨17932654146611850115299905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11955102764407900076866603 17932654146611850115299905)
                ·
                  refine ⟨13449490609958887586474929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17932654146611850115299905 13449490609958887586474929)
                  ·
                    refine ⟨10087117957469165689856197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13449490609958887586474929 10087117957469165689856197)
                    ·
                      refine ⟨1891334617025468566848037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10087117957469165689856197 1891334617025468566848037)
                      ·
                        rfl

theorem cell23_3683361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3683361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683361 prefixEnd_3683361 := by exact prefixLift 3683361
  have htrace : WordTrace (prefixWord ++ tailWord_3683361) baseStart_3683361 baseEnd_3683361 := by
    simpa [prefixWord, tailWord_3683361, baseEnd_3683361] using wordTrace_append hprefix tailTrace_3683361
  have hstable : (prefixWord ++ tailWord_3683361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683361).length < 2 ^ (prefixWord ++ tailWord_3683361).sum := by decide
  have hdescent : baseEnd_3683361 < baseStart_3683361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683388 : List Nat := [2, 2, 2, 2, 2, 2, 3, 3, 5]
def baseStart_3683388 : Nat := 118140960795 + 3683388 * 2 ^ 59
def prefixEnd_3683388 : Nat := 4983230072969 + 3 ^ 40 * 3683388 * 2
def baseEnd_3683388 : Nat := 210149831222571106801157

theorem tailTrace_3683388 : CollatzResearch.WordTrace tailWord_3683388 prefixEnd_3683388 210149831222571106801157 := by
  unfold tailWord_3683388
  simp only [CollatzResearch.WordTrace]
  refine ⟨67172098589860911716241409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89562798119814548954988545 67172098589860911716241409)
  ·
    refine ⟨50379073942395683787181057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67172098589860911716241409 50379073942395683787181057)
    ·
      refine ⟨37784305456796762840385793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50379073942395683787181057 37784305456796762840385793)
      ·
        refine ⟨28338229092597572130289345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37784305456796762840385793 28338229092597572130289345)
        ·
          refine ⟨21253671819448179097717009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28338229092597572130289345 21253671819448179097717009)
          ·
            refine ⟨15940253864586134323287757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21253671819448179097717009 15940253864586134323287757)
            ·
              refine ⟨5977595199219800371232909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15940253864586134323287757 5977595199219800371232909)
              ·
                refine ⟨2241598199707425139212341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5977595199219800371232909 2241598199707425139212341)
                ·
                  refine ⟨210149831222571106801157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2241598199707425139212341 210149831222571106801157)
                  ·
                    rfl

theorem cell23_3683388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 5].length) (baseStart_3683388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683388 prefixEnd_3683388 := by exact prefixLift 3683388
  have htrace : WordTrace (prefixWord ++ tailWord_3683388) baseStart_3683388 baseEnd_3683388 := by
    simpa [prefixWord, tailWord_3683388, baseEnd_3683388] using wordTrace_append hprefix tailTrace_3683388
  have hstable : (prefixWord ++ tailWord_3683388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683388).length < 2 ^ (prefixWord ++ tailWord_3683388).sum := by decide
  have hdescent : baseEnd_3683388 < baseStart_3683388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683391 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 1, 7, 2]
def baseStart_3683391 : Nat := 118140960795 + 3683391 * 2 ^ 59
def prefixEnd_3683391 : Nat := 4983230072969 + 3 ^ 40 * 3683391 * 2
def baseEnd_3683391 : Nat := 1891350021445103449472899

theorem tailTrace_3683391 : CollatzResearch.WordTrace tailWord_3683391 prefixEnd_3683391 1891350021445103449472899 := by
  unfold tailWord_3683391
  simp only [CollatzResearch.WordTrace]
  refine ⟨134344306598710954944842027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89562871065807303296561351 134344306598710954944842027)
  ·
    refine ⟨201516459898066432417263041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134344306598710954944842027 201516459898066432417263041)
    ·
      refine ⟨151137344923549824312947281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201516459898066432417263041 151137344923549824312947281)
      ·
        refine ⟨113353008692662368234710461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151137344923549824312947281 113353008692662368234710461)
        ·
          refine ⟨42507378259748388088016423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113353008692662368234710461 42507378259748388088016423)
          ·
            refine ⟨63761067389622582132024635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42507378259748388088016423 63761067389622582132024635)
            ·
              refine ⟨95641601084433873198036953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63761067389622582132024635 95641601084433873198036953)
              ·
                refine ⟨71731200813325404898527715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95641601084433873198036953 71731200813325404898527715)
                ·
                  refine ⟨107596801219988107347791573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71731200813325404898527715 107596801219988107347791573)
                  ·
                    refine ⟨2521800028593471265963865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 107596801219988107347791573 2521800028593471265963865)
                    ·
                      refine ⟨1891350021445103449472899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2521800028593471265963865 1891350021445103449472899)
                      ·
                        rfl

theorem cell23_3683391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 7, 2].length) (baseStart_3683391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683391 prefixEnd_3683391 := by exact prefixLift 3683391
  have htrace : WordTrace (prefixWord ++ tailWord_3683391) baseStart_3683391 baseEnd_3683391 := by
    simpa [prefixWord, tailWord_3683391, baseEnd_3683391] using wordTrace_append hprefix tailTrace_3683391
  have hstable : (prefixWord ++ tailWord_3683391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683391).length < 2 ^ (prefixWord ++ tailWord_3683391).sum := by decide
  have hdescent : baseEnd_3683391 < baseStart_3683391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683438 : List Nat := [4, 1, 2, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_3683438 : Nat := 118140960795 + 3683438 * 2 ^ 59
def prefixEnd_3683438 : Nat := 4983230072969 + 3 ^ 40 * 3683438 * 2
def baseEnd_3683438 : Nat := 1891374155035864765585183

theorem tailTrace_3683438 : CollatzResearch.WordTrace tailWord_3683438 prefixEnd_3683438 1891374155035864765585183 := by
  unfold tailWord_3683438
  simp only [CollatzResearch.WordTrace]
  refine ⟨16793252603692585246475371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89564013886360454647868645 16793252603692585246475371)
  ·
    refine ⟨25189878905538877869713057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16793252603692585246475371 25189878905538877869713057)
    ·
      refine ⟨18892409179154158402284793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25189878905538877869713057 18892409179154158402284793)
      ·
        refine ⟨14169306884365618801713595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18892409179154158402284793 14169306884365618801713595)
        ·
          refine ⟨21253960326548428202570393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14169306884365618801713595 21253960326548428202570393)
          ·
            refine ⟨15940470244911321151927795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21253960326548428202570393 15940470244911321151927795)
            ·
              refine ⟨23910705367366981727891693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15940470244911321151927795 23910705367366981727891693)
              ·
                refine ⟨8966514512762618147959385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23910705367366981727891693 8966514512762618147959385)
                ·
                  refine ⟨6724885884571963610969539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8966514512762618147959385 6724885884571963610969539)
                  ·
                    refine ⟨10087328826857945416454309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6724885884571963610969539 10087328826857945416454309)
                    ·
                      refine ⟨1891374155035864765585183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10087328826857945416454309 1891374155035864765585183)
                      ·
                        rfl

theorem cell23_3683438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_3683438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683438 prefixEnd_3683438 := by exact prefixLift 3683438
  have htrace : WordTrace (prefixWord ++ tailWord_3683438) baseStart_3683438 baseEnd_3683438 := by
    simpa [prefixWord, tailWord_3683438, baseEnd_3683438] using wordTrace_append hprefix tailTrace_3683438
  have hstable : (prefixWord ++ tailWord_3683438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683438).length < 2 ^ (prefixWord ++ tailWord_3683438).sum := by decide
  have hdescent : baseEnd_3683438 < baseStart_3683438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683465 : List Nat := [1, 2, 1, 1, 4, 4, 1, 4, 1, 4]
def baseStart_3683465 : Nat := 118140960795 + 3683465 * 2 ^ 59
def prefixEnd_3683465 : Nat := 4983230072969 + 3 ^ 40 * 3683465 * 2
def baseEnd_3683465 : Nat := 630462673004512053315853

theorem tailTrace_3683465 : CollatzResearch.WordTrace tailWord_3683465 prefixEnd_3683465 630462673004512053315853 := by
  unfold tailWord_3683465
  simp only [CollatzResearch.WordTrace]
  refine ⟨134347005600442865583035849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89564670400295243722023899 134347005600442865583035849)
  ·
    refine ⟨100760254200332149187276887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134347005600442865583035849 100760254200332149187276887)
    ·
      refine ⟨151140381300498223780915331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100760254200332149187276887 151140381300498223780915331)
      ·
        refine ⟨226710571950747335671372997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151140381300498223780915331 226710571950747335671372997)
        ·
          refine ⟨42508232240765125438382437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226710571950747335671372997 42508232240765125438382437)
          ·
            refine ⟨7970293545143461019696707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42508232240765125438382437 7970293545143461019696707)
            ·
              refine ⟨11955440317715191529545061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7970293545143461019696707 11955440317715191529545061)
              ·
                refine ⟨2241645059571598411789699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11955440317715191529545061 2241645059571598411789699)
                ·
                  refine ⟨3362467589357397617684549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2241645059571598411789699 3362467589357397617684549)
                  ·
                    refine ⟨630462673004512053315853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3362467589357397617684549 630462673004512053315853)
                    ·
                      rfl

theorem cell23_3683465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 1, 4].length) (baseStart_3683465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683465 prefixEnd_3683465 := by exact prefixLift 3683465
  have htrace : WordTrace (prefixWord ++ tailWord_3683465) baseStart_3683465 baseEnd_3683465 := by
    simpa [prefixWord, tailWord_3683465, baseEnd_3683465] using wordTrace_append hprefix tailTrace_3683465
  have hstable : (prefixWord ++ tailWord_3683465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683465).length < 2 ^ (prefixWord ++ tailWord_3683465).sum := by decide
  have hdescent : baseEnd_3683465 < baseStart_3683465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683531 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 3]
def baseStart_3683531 : Nat := 118140960795 + 3683531 * 2 ^ 59
def prefixEnd_3683531 : Nat := 4983230072969 + 3 ^ 40 * 3683531 * 2
def baseEnd_3683531 : Nat := 1891421908736732901722255

theorem tailTrace_3683531 : CollatzResearch.WordTrace tailWord_3683531 prefixEnd_3683531 1891421908736732901722255 := by
  unfold tailWord_3683531
  simp only [CollatzResearch.WordTrace]
  refine ⟨134349412818203758854938447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89566275212135839236625631 134349412818203758854938447)
  ·
    refine ⟨201524119227305638282407671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134349412818203758854938447 201524119227305638282407671)
    ·
      refine ⟨302286178840958457423611507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201524119227305638282407671 302286178840958457423611507)
      ·
        refine ⟨453429268261437686135417261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302286178840958457423611507 453429268261437686135417261)
        ·
          refine ⟨170035975598039132300781473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453429268261437686135417261 170035975598039132300781473)
          ·
            refine ⟨127526981698529349225586105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170035975598039132300781473 127526981698529349225586105)
            ·
              refine ⟨95645236273897011919189579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127526981698529349225586105 95645236273897011919189579)
              ·
                refine ⟨143467854410845517878784369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95645236273897011919189579 143467854410845517878784369)
                ·
                  refine ⟨107600890808134138409088277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143467854410845517878784369 107600890808134138409088277)
                  ·
                    refine ⟨5043791756631287737926013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107600890808134138409088277 5043791756631287737926013)
                    ·
                      refine ⟨1891421908736732901722255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5043791756631287737926013 1891421908736732901722255)
                      ·
                        rfl

theorem cell23_3683531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 3].length) (baseStart_3683531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683531 prefixEnd_3683531 := by exact prefixLift 3683531
  have htrace : WordTrace (prefixWord ++ tailWord_3683531) baseStart_3683531 baseEnd_3683531 := by
    simpa [prefixWord, tailWord_3683531, baseEnd_3683531] using wordTrace_append hprefix tailTrace_3683531
  have hstable : (prefixWord ++ tailWord_3683531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683531).length < 2 ^ (prefixWord ++ tailWord_3683531).sum := by decide
  have hdescent : baseEnd_3683531 < baseStart_3683531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683565 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_3683565 : Nat := 118140960795 + 3683565 * 2 ^ 59
def prefixEnd_3683565 : Nat := 4983230072969 + 3 ^ 40 * 3683565 * 2
def baseEnd_3683565 : Nat := 1891439367078985768697099

theorem tailTrace_3683565 : CollatzResearch.WordTrace tailWord_3683565 prefixEnd_3683565 1891439367078985768697099 := by
  unfold tailWord_3683565
  simp only [CollatzResearch.WordTrace]
  refine ⟨134350652900080582661676149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89567101933387055107784099 134350652900080582661676149)
  ·
    refine ⟨12595373709382554624532139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134350652900080582661676149 12595373709382554624532139)
    ·
      refine ⟨18893060564073831936798209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12595373709382554624532139 18893060564073831936798209)
      ·
        refine ⟨14169795423055373952598657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18893060564073831936798209 14169795423055373952598657)
        ·
          refine ⟨10627346567291530464448993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14169795423055373952598657 10627346567291530464448993)
          ·
            refine ⟨7970509925468647848336745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10627346567291530464448993 7970509925468647848336745)
            ·
              refine ⟨5977882444101485886252559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7970509925468647848336745 5977882444101485886252559)
              ·
                refine ⟨8966823666152228829378839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5977882444101485886252559 8966823666152228829378839)
                ·
                  refine ⟨13450235499228343244068259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8966823666152228829378839 13450235499228343244068259)
                  ·
                    refine ⟨20175353248842514866102389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13450235499228343244068259 20175353248842514866102389)
                    ·
                      refine ⟨1891439367078985768697099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20175353248842514866102389 1891439367078985768697099)
                      ·
                        rfl

theorem cell23_3683565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_3683565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683565 prefixEnd_3683565 := by exact prefixLift 3683565
  have htrace : WordTrace (prefixWord ++ tailWord_3683565) baseStart_3683565 baseEnd_3683565 := by
    simpa [prefixWord, tailWord_3683565, baseEnd_3683565] using wordTrace_append hprefix tailTrace_3683565
  have hstable : (prefixWord ++ tailWord_3683565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683565).length < 2 ^ (prefixWord ++ tailWord_3683565).sum := by decide
  have hdescent : baseEnd_3683565 < baseStart_3683565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683611 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 4, 6]
def baseStart_3683611 : Nat := 118140960795 + 3683611 * 2 ^ 59
def prefixEnd_3683611 : Nat := 4983230072969 + 3 ^ 40 * 3683611 * 2
def baseEnd_3683611 : Nat := 630487662396364196240629

theorem tailTrace_3683611 : CollatzResearch.WordTrace tailWord_3683611 prefixEnd_3683611 630487662396364196240629 := by
  unfold tailWord_3683611
  simp only [CollatzResearch.WordTrace]
  refine ⟨134352330657913932517850687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89568220438609288345233791 134352330657913932517850687)
  ·
    refine ⟨201528495986870898776776031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134352330657913932517850687 201528495986870898776776031)
    ·
      refine ⟨302292743980306348165164047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201528495986870898776776031 302292743980306348165164047)
      ·
        refine ⟨453439115970459522247746071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302292743980306348165164047 453439115970459522247746071)
        ·
          refine ⟨680158673955689283371619107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453439115970459522247746071 680158673955689283371619107)
          ·
            refine ⟨1020238010933533925057428661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680158673955689283371619107 1020238010933533925057428661)
            ·
              refine ⟨95647313525018805474133937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1020238010933533925057428661 95647313525018805474133937)
              ·
                refine ⟨71735485143764104105600453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95647313525018805474133937 71735485143764104105600453)
                ·
                  refine ⟨13450403464455769519800085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71735485143764104105600453 13450403464455769519800085)
                  ·
                    refine ⟨630487662396364196240629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13450403464455769519800085 630487662396364196240629)
                    ·
                      rfl

theorem cell23_3683611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 6].length) (baseStart_3683611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683611 prefixEnd_3683611 := by exact prefixLift 3683611
  have htrace : WordTrace (prefixWord ++ tailWord_3683611) baseStart_3683611 baseEnd_3683611 := by
    simpa [prefixWord, tailWord_3683611, baseEnd_3683611] using wordTrace_append hprefix tailTrace_3683611
  have hstable : (prefixWord ++ tailWord_3683611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683611).length < 2 ^ (prefixWord ++ tailWord_3683611).sum := by decide
  have hdescent : baseEnd_3683611 < baseStart_3683611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683629 : List Nat := [1, 5, 3, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_3683629 : Nat := 118140960795 + 3683629 * 2 ^ 59
def prefixEnd_3683629 : Nat := 4983230072969 + 3 ^ 40 * 3683629 * 2
def baseEnd_3683629 : Nat := 1891472229840873518296805

theorem tailTrace_3683629 : CollatzResearch.WordTrace tailWord_3683629 prefixEnd_3683629 1891472229840873518296805 := by
  unfold tailWord_3683629
  simp only [CollatzResearch.WordTrace]
  refine ⟨134352987171848721592005941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89568658114565814394670627 134352987171848721592005941)
  ·
    refine ⟨12595592547360817649250557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134352987171848721592005941 12595592547360817649250557)
    ·
      refine ⟨4723347205260306618468959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12595592547360817649250557 4723347205260306618468959)
      ·
        refine ⟨7085020807890459927703439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4723347205260306618468959 7085020807890459927703439)
        ·
          refine ⟨10627531211835689891555159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7085020807890459927703439 10627531211835689891555159)
          ·
            refine ⟨15941296817753534837332739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10627531211835689891555159 15941296817753534837332739)
            ·
              refine ⟨23911945226630302255999109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15941296817753534837332739 23911945226630302255999109)
              ·
                refine ⟨4483489729993181672999833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23911945226630302255999109 4483489729993181672999833)
                ·
                  refine ⟨3362617297494886254749875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4483489729993181672999833 3362617297494886254749875)
                  ·
                    refine ⟨5043925946242329382124813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3362617297494886254749875 5043925946242329382124813)
                    ·
                      refine ⟨1891472229840873518296805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5043925946242329382124813 1891472229840873518296805)
                      ·
                        rfl

theorem cell23_3683629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_3683629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683629 prefixEnd_3683629 := by exact prefixLift 3683629
  have htrace : WordTrace (prefixWord ++ tailWord_3683629) baseStart_3683629 baseEnd_3683629 := by
    simpa [prefixWord, tailWord_3683629, baseEnd_3683629] using wordTrace_append hprefix tailTrace_3683629
  have hstable : (prefixWord ++ tailWord_3683629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683629).length < 2 ^ (prefixWord ++ tailWord_3683629).sum := by decide
  have hdescent : baseEnd_3683629 < baseStart_3683629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683631 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 6]
def baseStart_3683631 : Nat := 118140960795 + 3683631 * 2 ^ 59
def prefixEnd_3683631 : Nat := 4983230072969 + 3 ^ 40 * 3683631 * 2
def baseEnd_3683631 : Nat := 1891473256802182510471795

theorem tailTrace_3683631 : CollatzResearch.WordTrace tailWord_3683631 prefixEnd_3683631 1891473256802182510471795 := by
  unfold tailWord_3683631
  simp only [CollatzResearch.WordTrace]
  refine ⟨134353060117841475933578747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89568706745227650622385831 134353060117841475933578747)
  ·
    refine ⟨201529590176762213900368121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134353060117841475933578747 201529590176762213900368121)
    ·
      refine ⟨151147192632571660425276091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201529590176762213900368121 151147192632571660425276091)
      ·
        refine ⟨226720788948857490637914137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151147192632571660425276091 226720788948857490637914137)
        ·
          refine ⟨170040591711643117978435603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226720788948857490637914137 170040591711643117978435603)
          ·
            refine ⟨255060887567464676967653405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170040591711643117978435603 255060887567464676967653405)
            ·
              refine ⟨95647832837799253862870027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255060887567464676967653405 95647832837799253862870027)
              ·
                refine ⟨143471749256698880794305041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95647832837799253862870027 143471749256698880794305041)
                ·
                  refine ⟨107603811942524160595728781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143471749256698880794305041 107603811942524160595728781)
                  ·
                    refine ⟨40351429478446560223398293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107603811942524160595728781 40351429478446560223398293)
                    ·
                      refine ⟨1891473256802182510471795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40351429478446560223398293 1891473256802182510471795)
                      ·
                        rfl

theorem cell23_3683631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_3683631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683631 prefixEnd_3683631 := by exact prefixLift 3683631
  have htrace : WordTrace (prefixWord ++ tailWord_3683631) baseStart_3683631 baseEnd_3683631 := by
    simpa [prefixWord, tailWord_3683631, baseEnd_3683631] using wordTrace_append hprefix tailTrace_3683631
  have hstable : (prefixWord ++ tailWord_3683631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683631).length < 2 ^ (prefixWord ++ tailWord_3683631).sum := by decide
  have hdescent : baseEnd_3683631 < baseStart_3683631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683648 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 4]
def baseStart_3683648 : Nat := 118140960795 + 3683648 * 2 ^ 59
def prefixEnd_3683648 : Nat := 4983230072969 + 3 ^ 40 * 3683648 * 2
def baseEnd_3683648 : Nat := 1891481985973308943959217

theorem tailTrace_3683648 : CollatzResearch.WordTrace tailWord_3683648 prefixEnd_3683648 1891481985973308943959217 := by
  unfold tailWord_3683648
  simp only [CollatzResearch.WordTrace]
  refine ⟨67176840079389943918473799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89569120105853258557965065 67176840079389943918473799)
  ·
    refine ⟨100765260119084915877710699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67176840079389943918473799 100765260119084915877710699)
    ·
      refine ⟨151147890178627373816566049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100765260119084915877710699 151147890178627373816566049)
      ·
        refine ⟨113360917633970530362424537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151147890178627373816566049 113360917633970530362424537)
        ·
          refine ⟨85020688225477897771818403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113360917633970530362424537 85020688225477897771818403)
          ·
            refine ⟨127531032338216846657727605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85020688225477897771818403 127531032338216846657727605)
            ·
              refine ⟨11956034281707829374161963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127531032338216846657727605 11956034281707829374161963)
              ·
                refine ⟨17934051422561744061242945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11956034281707829374161963 17934051422561744061242945)
                ·
                  refine ⟨13450538566921308045932209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17934051422561744061242945 13450538566921308045932209)
                  ·
                    refine ⟨10087903925190981034449157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13450538566921308045932209 10087903925190981034449157)
                    ·
                      refine ⟨1891481985973308943959217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10087903925190981034449157 1891481985973308943959217)
                      ·
                        rfl

theorem cell23_3683648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_3683648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683648 prefixEnd_3683648 := by exact prefixLift 3683648
  have htrace : WordTrace (prefixWord ++ tailWord_3683648) baseStart_3683648 baseEnd_3683648 := by
    simpa [prefixWord, tailWord_3683648, baseEnd_3683648] using wordTrace_append hprefix tailTrace_3683648
  have hstable : (prefixWord ++ tailWord_3683648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683648).length < 2 ^ (prefixWord ++ tailWord_3683648).sum := by decide
  have hdescent : baseEnd_3683648 < baseStart_3683648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683698 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_3683698 : Nat := 118140960795 + 3683698 * 2 ^ 59
def prefixEnd_3683698 : Nat := 4983230072969 + 3 ^ 40 * 3683698 * 2
def baseEnd_3683698 : Nat := 1891507660006033748333987

theorem tailTrace_3683698 : CollatzResearch.WordTrace tailWord_3683698 prefixEnd_3683698 1891507660006033748333987 := by
  unfold tailWord_3683698
  simp only [CollatzResearch.WordTrace]
  refine ⟨33588875952149686594066937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89570335872399164250845165 33588875952149686594066937)
  ·
    refine ⟨25191656964112264945550203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33588875952149686594066937 25191656964112264945550203)
    ·
      refine ⟨37787485446168397418325305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25191656964112264945550203 37787485446168397418325305)
      ·
        refine ⟨28340614084626298063743979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37787485446168397418325305 28340614084626298063743979)
        ·
          refine ⟨42510921126939447095615969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28340614084626298063743979 42510921126939447095615969)
          ·
            refine ⟨31883190845204585321711977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42510921126939447095615969 31883190845204585321711977)
            ·
              refine ⟨23912393133903438991283983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31883190845204585321711977 23912393133903438991283983)
              ·
                refine ⟨35868589700855158486925975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23912393133903438991283983 35868589700855158486925975)
                ·
                  refine ⟨53802884551282737730388963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35868589700855158486925975 53802884551282737730388963)
                  ·
                    refine ⟨80704326826924106595583445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53802884551282737730388963 80704326826924106595583445)
                    ·
                      refine ⟨1891507660006033748333987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80704326826924106595583445 1891507660006033748333987)
                      ·
                        rfl

theorem cell23_3683698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_3683698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683698 prefixEnd_3683698 := by exact prefixLift 3683698
  have htrace : WordTrace (prefixWord ++ tailWord_3683698) baseStart_3683698 baseEnd_3683698 := by
    simpa [prefixWord, tailWord_3683698, baseEnd_3683698] using wordTrace_append hprefix tailTrace_3683698
  have hstable : (prefixWord ++ tailWord_3683698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683698).length < 2 ^ (prefixWord ++ tailWord_3683698).sum := by decide
  have hdescent : baseEnd_3683698 < baseStart_3683698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683708 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_3683708 : Nat := 118140960795 + 3683708 * 2 ^ 59
def prefixEnd_3683708 : Nat := 4983230072969 + 3 ^ 40 * 3683708 * 2
def baseEnd_3683708 : Nat := 1891512794812578709208941

theorem tailTrace_3683708 : CollatzResearch.WordTrace tailWord_3683708 prefixEnd_3683708 1891512794812578709208941 := by
  unfold tailWord_3683708
  simp only [CollatzResearch.WordTrace]
  refine ⟨67177934269281259042065889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89570579025708345389421185 67177934269281259042065889)
  ·
    refine ⟨50383450701960944281549417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67177934269281259042065889 50383450701960944281549417)
    ·
      refine ⟨37787588026470708211162063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50383450701960944281549417 37787588026470708211162063)
      ·
        refine ⟨56681382039706062316743095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37787588026470708211162063 56681382039706062316743095)
        ·
          refine ⟨85022073059559093475114643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56681382039706062316743095 85022073059559093475114643)
          ·
            refine ⟨127533109589338640212671965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85022073059559093475114643 127533109589338640212671965)
            ·
              refine ⟨47824916096001990079751987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127533109589338640212671965 47824916096001990079751987)
              ·
                refine ⟨71737374144002985119627981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47824916096001990079751987 71737374144002985119627981)
                ·
                  refine ⟨26901515304001119419860493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71737374144002985119627981 26901515304001119419860493)
                  ·
                    refine ⟨10088068239000419782447685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26901515304001119419860493 10088068239000419782447685)
                    ·
                      refine ⟨1891512794812578709208941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10088068239000419782447685 1891512794812578709208941)
                      ·
                        rfl

theorem cell23_3683708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_3683708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683708 prefixEnd_3683708 := by exact prefixLift 3683708
  have htrace : WordTrace (prefixWord ++ tailWord_3683708) baseStart_3683708 baseEnd_3683708 := by
    simpa [prefixWord, tailWord_3683708, baseEnd_3683708] using wordTrace_append hprefix tailTrace_3683708
  have hstable : (prefixWord ++ tailWord_3683708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683708).length < 2 ^ (prefixWord ++ tailWord_3683708).sum := by decide
  have hdescent : baseEnd_3683708 < baseStart_3683708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683726 : List Nat := [4, 1, 1, 4, 3, 1, 1, 3, 5]
def baseStart_3683726 : Nat := 118140960795 + 3683726 * 2 ^ 59
def prefixEnd_3683726 : Nat := 4983230072969 + 3 ^ 40 * 3683726 * 2
def baseEnd_3683726 : Nat := 210169115273817737642651

theorem tailTrace_3683726 : CollatzResearch.WordTrace tailWord_3683726 prefixEnd_3683726 210169115273817737642651 := by
  unfold tailWord_3683726
  simp only [CollatzResearch.WordTrace]
  refine ⟨16794565631562163394785879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89571016701664871438858021 16794565631562163394785879)
  ·
    refine ⟨25191848447343245092178819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16794565631562163394785879 25191848447343245092178819)
    ·
      refine ⟨37787772671014867638268229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25191848447343245092178819 37787772671014867638268229)
      ·
        refine ⟨7085207375815287682175293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37787772671014867638268229 7085207375815287682175293)
        ·
          refine ⟨2656952765930732880815735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7085207375815287682175293 2656952765930732880815735)
          ·
            refine ⟨3985429148896099321223603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656952765930732880815735 3985429148896099321223603)
            ·
              refine ⟨5978143723344148981835405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3985429148896099321223603 5978143723344148981835405)
              ·
                refine ⟨2241803896254055868188277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5978143723344148981835405 2241803896254055868188277)
                ·
                  refine ⟨210169115273817737642651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2241803896254055868188277 210169115273817737642651)
                  ·
                    rfl

theorem cell23_3683726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_3683726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683726 prefixEnd_3683726 := by exact prefixLift 3683726
  have htrace : WordTrace (prefixWord ++ tailWord_3683726) baseStart_3683726 baseEnd_3683726 := by
    simpa [prefixWord, tailWord_3683726, baseEnd_3683726] using wordTrace_append hprefix tailTrace_3683726
  have hstable : (prefixWord ++ tailWord_3683726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683726).length < 2 ^ (prefixWord ++ tailWord_3683726).sum := by decide
  have hdescent : baseEnd_3683726 < baseStart_3683726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683768 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_3683768 : Nat := 118140960795 + 3683768 * 2 ^ 59
def prefixEnd_3683768 : Nat := 4983230072969 + 3 ^ 40 * 3683768 * 2
def baseEnd_3683768 : Nat := 1891543603651848474458665

theorem tailTrace_3683768 : CollatzResearch.WordTrace tailWord_3683768 prefixEnd_3683768 1891543603651848474458665 := by
  unfold tailWord_3683768
  simp only [CollatzResearch.WordTrace]
  refine ⟨67179028459172574165657979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89572037945563432220877305 67179028459172574165657979)
  ·
    refine ⟨100768542688758861248486969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67179028459172574165657979 100768542688758861248486969)
    ·
      refine ⟨75576407016569145936365227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100768542688758861248486969 75576407016569145936365227)
      ·
        refine ⟨113364610524853718904547841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75576407016569145936365227 113364610524853718904547841)
        ·
          refine ⟨85023457893640289178410881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113364610524853718904547841 85023457893640289178410881)
          ·
            refine ⟨63767593420230216883808161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85023457893640289178410881 63767593420230216883808161)
            ·
              refine ⟨47825695065172662662856121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63767593420230216883808161 47825695065172662662856121)
              ·
                refine ⟨35869271298879496997142091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47825695065172662662856121 35869271298879496997142091)
                ·
                  refine ⟨53803906948319245495713137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35869271298879496997142091 53803906948319245495713137)
                  ·
                    refine ⟨40352930211239434121784853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53803906948319245495713137 40352930211239434121784853)
                    ·
                      refine ⟨1891543603651848474458665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40352930211239434121784853 1891543603651848474458665)
                      ·
                        rfl

theorem cell23_3683768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_3683768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683768 prefixEnd_3683768 := by exact prefixLift 3683768
  have htrace : WordTrace (prefixWord ++ tailWord_3683768) baseStart_3683768 baseEnd_3683768 := by
    simpa [prefixWord, tailWord_3683768, baseEnd_3683768] using wordTrace_append hprefix tailTrace_3683768
  have hstable : (prefixWord ++ tailWord_3683768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683768).length < 2 ^ (prefixWord ++ tailWord_3683768).sum := by decide
  have hdescent : baseEnd_3683768 < baseStart_3683768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683825 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 1, 6]
def baseStart_3683825 : Nat := 118140960795 + 3683825 * 2 ^ 59
def prefixEnd_3683825 : Nat := 4983230072969 + 3 ^ 40 * 3683825 * 2
def baseEnd_3683825 : Nat := 630524290683051583815301

theorem tailTrace_3683825 : CollatzResearch.WordTrace tailWord_3683825 prefixEnd_3683825 630524290683051583815301 := by
  unfold tailWord_3683825
  simp only [CollatzResearch.WordTrace]
  refine ⟨134360135879138647066140929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89573423919425764710760619 134360135879138647066140929)
  ·
    refine ⟨100770101909353985299605697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134360135879138647066140929 100770101909353985299605697)
    ·
      refine ⟨75577576432015488974704273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100770101909353985299605697 75577576432015488974704273)
      ·
        refine ⟨56683182324011616731028205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75577576432015488974704273 56683182324011616731028205)
        ·
          refine ⟨21256193371504356274135577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56683182324011616731028205 21256193371504356274135577)
          ·
            refine ⟨15942145028628267205601683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21256193371504356274135577 15942145028628267205601683)
            ·
              refine ⟨23913217542942400808402525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15942145028628267205601683 23913217542942400808402525)
              ·
                refine ⟨8967456578603400303150947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23913217542942400808402525 8967456578603400303150947)
                ·
                  refine ⟨13451184867905100454726421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8967456578603400303150947 13451184867905100454726421)
                  ·
                    refine ⟨630524290683051583815301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13451184867905100454726421 630524290683051583815301)
                    ·
                      rfl

theorem cell23_3683825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_3683825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683825 prefixEnd_3683825 := by exact prefixLift 3683825
  have htrace : WordTrace (prefixWord ++ tailWord_3683825) baseStart_3683825 baseEnd_3683825 := by
    simpa [prefixWord, tailWord_3683825, baseEnd_3683825] using wordTrace_append hprefix tailTrace_3683825
  have hstable : (prefixWord ++ tailWord_3683825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683825).length < 2 ^ (prefixWord ++ tailWord_3683825).sum := by decide
  have hdescent : baseEnd_3683825 < baseStart_3683825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683859 : List Nat := [1, 1, 1, 2, 1, 8, 1, 2, 2, 4]
def baseStart_3683859 : Nat := 118140960795 + 3683859 * 2 ^ 59
def prefixEnd_3683859 : Nat := 4983230072969 + 3 ^ 40 * 3683859 * 2
def baseEnd_3683859 : Nat := 630530110130469206140249

theorem tailTrace_3683859 : CollatzResearch.WordTrace tailWord_3683859 prefixEnd_3683859 630530110130469206140249 := by
  unfold tailWord_3683859
  simp only [CollatzResearch.WordTrace]
  refine ⟨134361375961015470872878631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89574250640676980581919087 134361375961015470872878631)
  ·
    refine ⟨201542063941523206309317947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134361375961015470872878631 201542063941523206309317947)
    ·
      refine ⟨302313095912284809463976921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201542063941523206309317947 302313095912284809463976921)
      ·
        refine ⟨226734821934213607097982691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302313095912284809463976921 226734821934213607097982691)
        ·
          refine ⟨340102232901320410646974037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226734821934213607097982691 340102232901320410646974037)
          ·
            refine ⟨3985573041812348562269227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 340102232901320410646974037 3985573041812348562269227)
            ·
              refine ⟨5978359562718522843403841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3985573041812348562269227 5978359562718522843403841)
              ·
                refine ⟨4483769672038892132552881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5978359562718522843403841 4483769672038892132552881)
                ·
                  refine ⟨3362827254029169099414661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4483769672038892132552881 3362827254029169099414661)
                  ·
                    refine ⟨630530110130469206140249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3362827254029169099414661 630530110130469206140249)
                    ·
                      rfl

theorem cell23_3683859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 4].length) (baseStart_3683859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683859 prefixEnd_3683859 := by exact prefixLift 3683859
  have htrace : WordTrace (prefixWord ++ tailWord_3683859) baseStart_3683859 baseEnd_3683859 := by
    simpa [prefixWord, tailWord_3683859, baseEnd_3683859] using wordTrace_append hprefix tailTrace_3683859
  have hstable : (prefixWord ++ tailWord_3683859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683859).length < 2 ^ (prefixWord ++ tailWord_3683859).sum := by decide
  have hdescent : baseEnd_3683859 < baseStart_3683859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683886 : List Nat := [4, 1, 3, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_3683886 : Nat := 118140960795 + 3683886 * 2 ^ 59
def prefixEnd_3683886 : Nat := 4983230072969 + 3 ^ 40 * 3683886 * 2
def baseEnd_3683886 : Nat := 1891604194369079012783123

theorem tailTrace_3683886 : CollatzResearch.WordTrace tailWord_3683886 prefixEnd_3683886 1891604194369079012783123 := by
  unfold tailWord_3683886
  simp only [CollatzResearch.WordTrace]
  refine ⟨16795295091489706810513939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89574907154611769656074341 16795295091489706810513939)
  ·
    refine ⟨25192942637234560215770909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16795295091489706810513939 25192942637234560215770909)
    ·
      refine ⟨9447353488962960080914091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25192942637234560215770909 9447353488962960080914091)
      ·
        refine ⟨14171030233444440121371137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9447353488962960080914091 14171030233444440121371137)
        ·
          refine ⟨10628272675083330091028353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14171030233444440121371137 10628272675083330091028353)
          ·
            refine ⟨7971204506312497568271265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10628272675083330091028353 7971204506312497568271265)
            ·
              refine ⟨5978403379734373176203449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7971204506312497568271265 5978403379734373176203449)
              ·
                refine ⟨4483802534800779882152587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5978403379734373176203449 4483802534800779882152587)
                ·
                  refine ⟨6725703802201169823228881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4483802534800779882152587 6725703802201169823228881)
                  ·
                    refine ⟨5044277851650877367421661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6725703802201169823228881 5044277851650877367421661)
                    ·
                      refine ⟨1891604194369079012783123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5044277851650877367421661 1891604194369079012783123)
                      ·
                        rfl

theorem cell23_3683886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_3683886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683886 prefixEnd_3683886 := by exact prefixLift 3683886
  have htrace : WordTrace (prefixWord ++ tailWord_3683886) baseStart_3683886 baseEnd_3683886 := by
    simpa [prefixWord, tailWord_3683886, baseEnd_3683886] using wordTrace_append hprefix tailTrace_3683886
  have hstable : (prefixWord ++ tailWord_3683886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683886).length < 2 ^ (prefixWord ++ tailWord_3683886).sum := by decide
  have hdescent : baseEnd_3683886 < baseStart_3683886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683895 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 5]
def baseStart_3683895 : Nat := 118140960795 + 3683895 * 2 ^ 59
def prefixEnd_3683895 : Nat := 4983230072969 + 3 ^ 40 * 3683895 * 2
def baseEnd_3683895 : Nat := 1891608815694969477570581

theorem tailTrace_3683895 : CollatzResearch.WordTrace tailWord_3683895 prefixEnd_3683895 1891608815694969477570581 := by
  unfold tailWord_3683895
  simp only [CollatzResearch.WordTrace]
  refine ⟨134362688988885049021189139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89575125992590032680792759 134362688988885049021189139)
  ·
    refine ⟨201544033483327573531783709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134362688988885049021189139 201544033483327573531783709)
    ·
      refine ⟨75579012556247840074418891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201544033483327573531783709 75579012556247840074418891)
      ·
        refine ⟨113368518834371760111628337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75579012556247840074418891 113368518834371760111628337)
        ·
          refine ⟨85026389125778820083721253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113368518834371760111628337 85026389125778820083721253)
          ·
            refine ⟨15942447961083528765697735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85026389125778820083721253 15942447961083528765697735)
            ·
              refine ⟨23913671941625293148546603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15942447961083528765697735 23913671941625293148546603)
              ·
                refine ⟨35870507912437939722819905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23913671941625293148546603 35870507912437939722819905)
                ·
                  refine ⟨26902880934328454792114929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35870507912437939722819905 26902880934328454792114929)
                  ·
                    refine ⟨20177160700746341094086197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26902880934328454792114929 20177160700746341094086197)
                    ·
                      refine ⟨1891608815694969477570581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20177160700746341094086197 1891608815694969477570581)
                      ·
                        rfl

theorem cell23_3683895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_3683895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683895 prefixEnd_3683895 := by exact prefixLift 3683895
  have htrace : WordTrace (prefixWord ++ tailWord_3683895) baseStart_3683895 baseEnd_3683895 := by
    simpa [prefixWord, tailWord_3683895, baseEnd_3683895] using wordTrace_append hprefix tailTrace_3683895
  have hstable : (prefixWord ++ tailWord_3683895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683895).length < 2 ^ (prefixWord ++ tailWord_3683895).sum := by decide
  have hdescent : baseEnd_3683895 < baseStart_3683895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683900 : List Nat := [2, 2, 2, 2, 4, 2, 1, 3, 1, 2, 2]
def baseStart_3683900 : Nat := 118140960795 + 3683900 * 2 ^ 59
def prefixEnd_3683900 : Nat := 4983230072969 + 3 ^ 40 * 3683900 * 2
def baseEnd_3683900 : Nat := 1891611383098241958008059

theorem tailTrace_3683900 : CollatzResearch.WordTrace tailWord_3683900 prefixEnd_3683900 1891611383098241958008059 := by
  unfold tailWord_3683900
  simp only [CollatzResearch.WordTrace]
  refine ⟨67181435676933467437560577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89575247569244623250080769 67181435676933467437560577)
  ·
    refine ⟨50386076757700100578170433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67181435676933467437560577 50386076757700100578170433)
    ·
      refine ⟨37789557568275075433627825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50386076757700100578170433 37789557568275075433627825)
      ·
        refine ⟨28342168176206306575220869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37789557568275075433627825 28342168176206306575220869)
        ·
          refine ⟨5314156533038682482853913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28342168176206306575220869 5314156533038682482853913)
          ·
            refine ⟨3985617399779011862140435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5314156533038682482853913 3985617399779011862140435)
            ·
              refine ⟨5978426099668517793210653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3985617399779011862140435 5978426099668517793210653)
              ·
                refine ⟨2241909787375694172453995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5978426099668517793210653 2241909787375694172453995)
                ·
                  refine ⟨3362864681063541258680993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2241909787375694172453995 3362864681063541258680993)
                  ·
                    refine ⟨2522148510797655944010745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3362864681063541258680993 2522148510797655944010745)
                    ·
                      refine ⟨1891611383098241958008059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2522148510797655944010745 1891611383098241958008059)
                      ·
                        rfl

theorem cell23_3683900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_3683900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683900 prefixEnd_3683900 := by exact prefixLift 3683900
  have htrace : WordTrace (prefixWord ++ tailWord_3683900) baseStart_3683900 baseEnd_3683900 := by
    simpa [prefixWord, tailWord_3683900, baseEnd_3683900] using wordTrace_append hprefix tailTrace_3683900
  have hstable : (prefixWord ++ tailWord_3683900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683900).length < 2 ^ (prefixWord ++ tailWord_3683900).sum := by decide
  have hdescent : baseEnd_3683900 < baseStart_3683900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683909 : List Nat := [1, 3, 1, 1, 1, 4, 1, 5, 1, 3, 2]
def baseStart_3683909 : Nat := 118140960795 + 3683909 * 2 ^ 59
def prefixEnd_3683909 : Nat := 4983230072969 + 3 ^ 40 * 3683909 * 2
def baseEnd_3683909 : Nat := 1891616004424132422795517

theorem tailTrace_3683909 : CollatzResearch.WordTrace tailWord_3683909 prefixEnd_3683909 1891616004424132422795517 := by
  unfold tailWord_3683909
  simp only [CollatzResearch.WordTrace]
  refine ⟨134363199610834329412198781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89575466407222886274799187 134363199610834329412198781)
  ·
    refine ⟨50386199854062873529574543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134363199610834329412198781 50386199854062873529574543)
    ·
      refine ⟨75579299781094310294361815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50386199854062873529574543 75579299781094310294361815)
      ·
        refine ⟨113368949671641465441542723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75579299781094310294361815 113368949671641465441542723)
        ·
          refine ⟨170053424507462198162314085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113368949671641465441542723 170053424507462198162314085)
          ·
            refine ⟨31885017095149162155433891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170053424507462198162314085 31885017095149162155433891)
            ·
              refine ⟨47827525642723743233150837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31885017095149162155433891 47827525642723743233150837)
              ·
                refine ⟨4483830529005350928107891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47827525642723743233150837 4483830529005350928107891)
                ·
                  refine ⟨6725745793508026392161837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4483830529005350928107891 6725745793508026392161837)
                  ·
                    refine ⟨2522154672565509897060689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6725745793508026392161837 2522154672565509897060689)
                    ·
                      refine ⟨1891616004424132422795517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2522154672565509897060689 1891616004424132422795517)
                      ·
                        rfl

theorem cell23_3683909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 3, 2].length) (baseStart_3683909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683909 prefixEnd_3683909 := by exact prefixLift 3683909
  have htrace : WordTrace (prefixWord ++ tailWord_3683909) baseStart_3683909 baseEnd_3683909 := by
    simpa [prefixWord, tailWord_3683909, baseEnd_3683909] using wordTrace_append hprefix tailTrace_3683909
  have hstable : (prefixWord ++ tailWord_3683909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683909).length < 2 ^ (prefixWord ++ tailWord_3683909).sum := by decide
  have hdescent : baseEnd_3683909 < baseStart_3683909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683917 : List Nat := [1, 6, 1, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_3683917 : Nat := 118140960795 + 3683917 * 2 ^ 59
def prefixEnd_3683917 : Nat := 4983230072969 + 3 ^ 40 * 3683917 * 2
def baseEnd_3683917 : Nat := 1891620112269368391495481

theorem tailTrace_3683917 : CollatzResearch.WordTrace tailWord_3683917 prefixEnd_3683917 1891620112269368391495481 := by
  unfold tailWord_3683917
  simp only [CollatzResearch.WordTrace]
  refine ⟨134363491394805346778490005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89575660929870231185660003 134363491394805346778490005)
  ·
    refine ⟨6298288659131500630241719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134363491394805346778490005 6298288659131500630241719)
    ·
      refine ⟨9447432988697250945362579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6298288659131500630241719 9447432988697250945362579)
      ·
        refine ⟨14171149483045876418043869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9447432988697250945362579 14171149483045876418043869)
        ·
          refine ⟨5314181056142203656766451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14171149483045876418043869 5314181056142203656766451)
          ·
            refine ⟨7971271584213305485149677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5314181056142203656766451 7971271584213305485149677)
            ·
              refine ⟨2989226844079989556931129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7971271584213305485149677 2989226844079989556931129)
              ·
                refine ⟨2241920133059992167698347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2989226844079989556931129 2241920133059992167698347)
                ·
                  refine ⟨3362880199589988251547521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2241920133059992167698347 3362880199589988251547521)
                  ·
                    refine ⟨2522160149692491188660641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3362880199589988251547521 2522160149692491188660641)
                    ·
                      refine ⟨1891620112269368391495481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2522160149692491188660641 1891620112269368391495481)
                      ·
                        rfl

theorem cell23_3683917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_3683917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683917 prefixEnd_3683917 := by exact prefixLift 3683917
  have htrace : WordTrace (prefixWord ++ tailWord_3683917) baseStart_3683917 baseEnd_3683917 := by
    simpa [prefixWord, tailWord_3683917, baseEnd_3683917] using wordTrace_append hprefix tailTrace_3683917
  have hstable : (prefixWord ++ tailWord_3683917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683917).length < 2 ^ (prefixWord ++ tailWord_3683917).sum := by decide
  have hdescent : baseEnd_3683917 < baseStart_3683917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683925 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_3683925 : Nat := 118140960795 + 3683925 * 2 ^ 59
def prefixEnd_3683925 : Nat := 4983230072969 + 3 ^ 40 * 3683925 * 2
def baseEnd_3683925 : Nat := 1891624220114604360195443

theorem tailTrace_3683925 : CollatzResearch.WordTrace tailWord_3683925 prefixEnd_3683925 1891624220114604360195443 := by
  unfold tailWord_3683925
  simp only [CollatzResearch.WordTrace]
  refine ⟨134363783178776364144781229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89575855452517576096520819 134363783178776364144781229)
  ·
    refine ⟨50386418692041136554292961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134363783178776364144781229 50386418692041136554292961)
    ·
      refine ⟨37789814019030852415719721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50386418692041136554292961 37789814019030852415719721)
      ·
        refine ⟨28342360514273139311789791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37789814019030852415719721 28342360514273139311789791)
        ·
          refine ⟨42513540771409708967684687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28342360514273139311789791 42513540771409708967684687)
          ·
            refine ⟨63770311157114563451527031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42513540771409708967684687 63770311157114563451527031)
            ·
              refine ⟨95655466735671845177290547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63770311157114563451527031 95655466735671845177290547)
              ·
                refine ⟨143483200103507767765935821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95655466735671845177290547 143483200103507767765935821)
                ·
                  refine ⟨53806200038815412912225933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143483200103507767765935821 53806200038815412912225933)
                  ·
                    refine ⟨20177325014555779842084725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53806200038815412912225933 20177325014555779842084725)
                    ·
                      refine ⟨1891624220114604360195443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20177325014555779842084725 1891624220114604360195443)
                      ·
                        rfl

theorem cell23_3683925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_3683925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3683925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3683925 prefixEnd_3683925 := by exact prefixLift 3683925
  have htrace : WordTrace (prefixWord ++ tailWord_3683925) baseStart_3683925 baseEnd_3683925 := by
    simpa [prefixWord, tailWord_3683925, baseEnd_3683925] using wordTrace_append hprefix tailTrace_3683925
  have hstable : (prefixWord ++ tailWord_3683925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683925).length < 2 ^ (prefixWord ++ tailWord_3683925).sum := by decide
  have hdescent : baseEnd_3683925 < baseStart_3683925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
