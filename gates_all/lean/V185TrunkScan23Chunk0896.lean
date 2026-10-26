import V185TrunkScan23Chunk0895

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5303725 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_5303725 : Nat := 118140960795 + 5303725 * 2 ^ 59
def prefixEnd_5303725 : Nat := 4983230072969 + 3 ^ 40 * 5303725 * 2
def baseEnd_5303725 : Nat := 2723360184267366885246119

theorem tailTrace_5303725 : CollatzResearch.WordTrace tailWord_5303725 prefixEnd_5303725 2723360184267366885246119 := by
  unfold tailWord_5303725
  simp only [CollatzResearch.WordTrace]
  refine ⟨193442742710517603960360629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128961828473678402640240419 193442742710517603960360629)
  ·
    refine ⟨18135257129111025371283809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193442742710517603960360629 18135257129111025371283809)
    ·
      refine ⟨13601442846833269028462857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18135257129111025371283809 13601442846833269028462857)
      ·
        refine ⟨10201082135124951771347143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13601442846833269028462857 10201082135124951771347143)
        ·
          refine ⟨15301623202687427657020715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10201082135124951771347143 15301623202687427657020715)
          ·
            refine ⟨22952434804031141485531073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15301623202687427657020715 22952434804031141485531073)
            ·
              refine ⟨17214326103023356114148305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22952434804031141485531073 17214326103023356114148305)
              ·
                refine ⟨12910744577267517085611229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17214326103023356114148305 12910744577267517085611229)
                ·
                  refine ⟨4841529216475318907104211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12910744577267517085611229 4841529216475318907104211)
                  ·
                    refine ⟨7262293824712978360656317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4841529216475318907104211 7262293824712978360656317)
                    ·
                      refine ⟨2723360184267366885246119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7262293824712978360656317 2723360184267366885246119)
                      ·
                        rfl

theorem cell23_5303725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_5303725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303725 prefixEnd_5303725 := by exact prefixLift 5303725
  have htrace : WordTrace (prefixWord ++ tailWord_5303725) baseStart_5303725 baseEnd_5303725 := by
    simpa [prefixWord, tailWord_5303725, baseEnd_5303725] using wordTrace_append hprefix tailTrace_5303725
  have hstable : (prefixWord ++ tailWord_5303725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303725).length < 2 ^ (prefixWord ++ tailWord_5303725).sum := by decide
  have hdescent : baseEnd_5303725 < baseStart_5303725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303741 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 6, 4]
def baseStart_5303741 : Nat := 118140960795 + 5303741 * 2 ^ 59
def prefixEnd_5303741 : Nat := 4983230072969 + 3 ^ 40 * 5303741 * 2
def baseEnd_5303741 : Nat := 907789466652612940882015

theorem tailTrace_5303741 : CollatzResearch.WordTrace tailWord_5303741 prefixEnd_5303741 907789466652612940882015 := by
  unfold tailWord_5303741
  simp only [CollatzResearch.WordTrace]
  refine ⟨193443326278459638692943077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128962217518973092461962051 193443326278459638692943077)
  ·
    refine ⟨36270623677211182254926827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193443326278459638692943077 36270623677211182254926827)
    ·
      refine ⟨54405935515816773382390241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36270623677211182254926827 54405935515816773382390241)
      ·
        refine ⟨40804451636862580036792681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54405935515816773382390241 40804451636862580036792681)
        ·
          refine ⟨30603338727646935027594511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40804451636862580036792681 30603338727646935027594511)
          ·
            refine ⟨45905008091470402541391767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30603338727646935027594511 45905008091470402541391767)
            ·
              refine ⟨68857512137205603812087651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45905008091470402541391767 68857512137205603812087651)
              ·
                refine ⟨103286268205808405718131477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68857512137205603812087651 103286268205808405718131477)
                ·
                  refine ⟨4841543822147269018037413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103286268205808405718131477 4841543822147269018037413)
                  ·
                    refine ⟨907789466652612940882015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4841543822147269018037413 907789466652612940882015)
                    ·
                      rfl

theorem cell23_5303741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_5303741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303741 prefixEnd_5303741 := by exact prefixLift 5303741
  have htrace : WordTrace (prefixWord ++ tailWord_5303741) baseStart_5303741 baseEnd_5303741 := by
    simpa [prefixWord, tailWord_5303741, baseEnd_5303741] using wordTrace_append hprefix tailTrace_5303741
  have hstable : (prefixWord ++ tailWord_5303741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303741).length < 2 ^ (prefixWord ++ tailWord_5303741).sum := by decide
  have hdescent : baseEnd_5303741 < baseStart_5303741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303751 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 5]
def baseStart_5303751 : Nat := 118140960795 + 5303751 * 2 ^ 59
def prefixEnd_5303751 : Nat := 4983230072969 + 3 ^ 40 * 5303751 * 2
def baseEnd_5303751 : Nat := 2723373534764383783520999

theorem tailTrace_5303751 : CollatzResearch.WordTrace tailWord_5303751 prefixEnd_5303751 2723373534764383783520999 := by
  unfold tailWord_5303751
  simp only [CollatzResearch.WordTrace]
  refine ⟨193443691008423410400807107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128962460672282273600538071 193443691008423410400807107)
  ·
    refine ⟨290165536512635115601210661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193443691008423410400807107 290165536512635115601210661)
    ·
      refine ⟨54406038096119084175226999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290165536512635115601210661 54406038096119084175226999)
      ·
        refine ⟨81609057144178626262840499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54406038096119084175226999 81609057144178626262840499)
        ·
          refine ⟨122413585716267939394260749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81609057144178626262840499 122413585716267939394260749)
          ·
            refine ⟨45905094643600477272847781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122413585716267939394260749 45905094643600477272847781)
            ·
              refine ⟨8607205245675089488658959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45905094643600477272847781 8607205245675089488658959)
              ·
                refine ⟨12910807868512634232988439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8607205245675089488658959 12910807868512634232988439)
                ·
                  refine ⟨19366211802768951349482659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12910807868512634232988439 19366211802768951349482659)
                  ·
                    refine ⟨29049317704153427024223989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19366211802768951349482659 29049317704153427024223989)
                    ·
                      refine ⟨2723373534764383783520999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29049317704153427024223989 2723373534764383783520999)
                      ·
                        rfl

theorem cell23_5303751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_5303751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303751 prefixEnd_5303751 := by exact prefixLift 5303751
  have htrace : WordTrace (prefixWord ++ tailWord_5303751) baseStart_5303751 baseEnd_5303751 := by
    simpa [prefixWord, tailWord_5303751, baseEnd_5303751] using wordTrace_append hprefix tailTrace_5303751
  have hstable : (prefixWord ++ tailWord_5303751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303751).length < 2 ^ (prefixWord ++ tailWord_5303751).sum := by decide
  have hdescent : baseEnd_5303751 < baseStart_5303751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303754 : List Nat := [3, 1, 2, 1, 2, 3, 11]
def baseStart_5303754 : Nat := 118140960795 + 5303754 * 2 ^ 59
def prefixEnd_5303754 : Nat := 4983230072969 + 3 ^ 40 * 5303754 * 2
def baseEnd_5303754 : Nat := 33621914508720336688685

theorem tailTrace_5303754 : CollatzResearch.WordTrace tailWord_5303754 prefixEnd_5303754 33621914508720336688685 := by
  unfold tailWord_5303754
  simp only [CollatzResearch.WordTrace]
  refine ⟨48360950106853135478291579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128962533618275027942110877 48360950106853135478291579)
  ·
    refine ⟨72541425160279703217437369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48360950106853135478291579 72541425160279703217437369)
    ·
      refine ⟨54406068870209777413078027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72541425160279703217437369 54406068870209777413078027)
      ·
        refine ⟨81609103305314666119617041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54406068870209777413078027 81609103305314666119617041)
        ·
          refine ⟨61206827478985999589712781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81609103305314666119617041 61206827478985999589712781)
          ·
            refine ⟨22952560304619749846142293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61206827478985999589712781 22952560304619749846142293)
            ·
              refine ⟨33621914508720336688685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 22952560304619749846142293 33621914508720336688685)
              ·
                rfl

theorem cell23_5303754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 11].length) (baseStart_5303754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303754 prefixEnd_5303754 := by exact prefixLift 5303754
  have htrace : WordTrace (prefixWord ++ tailWord_5303754) baseStart_5303754 baseEnd_5303754 := by
    simpa [prefixWord, tailWord_5303754, baseEnd_5303754] using wordTrace_append hprefix tailTrace_5303754
  have hstable : (prefixWord ++ tailWord_5303754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303754).length < 2 ^ (prefixWord ++ tailWord_5303754).sum := by decide
  have hdescent : baseEnd_5303754 < baseStart_5303754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303798 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_5303798 : Nat := 118140960795 + 5303798 * 2 ^ 59
def prefixEnd_5303798 : Nat := 4983230072969 + 3 ^ 40 * 5303798 * 2
def baseEnd_5303798 : Nat := 2723397668355145099633283

theorem tailTrace_5303798 : CollatzResearch.WordTrace tailWord_5303798 prefixEnd_5303798 2723397668355145099633283 := by
  unfold tailWord_5303798
  simp only [CollatzResearch.WordTrace]
  refine ⟨12090337827453321089235503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128963603492835424951845365 12090337827453321089235503)
  ·
    refine ⟨18135506741179981633853255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12090337827453321089235503 18135506741179981633853255)
    ·
      refine ⟨27203260111769972450779883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18135506741179981633853255 27203260111769972450779883)
      ·
        refine ⟨40804890167654958676169825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27203260111769972450779883 40804890167654958676169825)
        ·
          refine ⟨30603667625741219007127369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40804890167654958676169825 30603667625741219007127369)
          ·
            refine ⟨22952750719305914255345527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30603667625741219007127369 22952750719305914255345527)
            ·
              refine ⟨34429126078958871383018291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22952750719305914255345527 34429126078958871383018291)
              ·
                refine ⟨51643689118438307074527437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34429126078958871383018291 51643689118438307074527437)
                ·
                  refine ⟨19366383419414365152947789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51643689118438307074527437 19366383419414365152947789)
                  ·
                    refine ⟨7262393782280386932355421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19366383419414365152947789 7262393782280386932355421)
                    ·
                      refine ⟨2723397668355145099633283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7262393782280386932355421 2723397668355145099633283)
                      ·
                        rfl

theorem cell23_5303798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_5303798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303798 prefixEnd_5303798 := by exact prefixLift 5303798
  have htrace : WordTrace (prefixWord ++ tailWord_5303798) baseStart_5303798 baseEnd_5303798 := by
    simpa [prefixWord, tailWord_5303798, baseEnd_5303798] using wordTrace_append hprefix tailTrace_5303798
  have hstable : (prefixWord ++ tailWord_5303798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303798).length < 2 ^ (prefixWord ++ tailWord_5303798).sum := by decide
  have hdescent : baseEnd_5303798 < baseStart_5303798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303815 : List Nat := [1, 1, 4, 3, 2, 1, 1, 4, 2, 1, 3]
def baseStart_5303815 : Nat := 118140960795 + 5303815 * 2 ^ 59
def prefixEnd_5303815 : Nat := 4983230072969 + 3 ^ 40 * 5303815 * 2
def baseEnd_5303815 : Nat := 2723406397526271533120705

theorem tailTrace_5303815 : CollatzResearch.WordTrace tailWord_5303815 prefixEnd_5303815 2723406397526271533120705 := by
  unfold tailWord_5303815
  simp only [CollatzResearch.WordTrace]
  refine ⟨193446025280191549331136899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128964016853461032887424599 193446025280191549331136899)
  ·
    refine ⟨290169037920287323996705349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193446025280191549331136899 290169037920287323996705349)
    ·
      refine ⟨54406694610053873249382253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290169037920287323996705349 54406694610053873249382253)
      ·
        refine ⟨20402510478770202468518345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54406694610053873249382253 20402510478770202468518345)
        ·
          refine ⟨15301882859077651851388759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20402510478770202468518345 15301882859077651851388759)
          ·
            refine ⟨22952824288616477777083139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15301882859077651851388759 22952824288616477777083139)
            ·
              refine ⟨34429236432924716665624709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22952824288616477777083139 34429236432924716665624709)
              ·
                refine ⟨6455481831173384374804633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34429236432924716665624709 6455481831173384374804633)
                ·
                  refine ⟨4841611373380038281103475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6455481831173384374804633 4841611373380038281103475)
                  ·
                    refine ⟨7262417060070057421655213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4841611373380038281103475 7262417060070057421655213)
                    ·
                      refine ⟨2723406397526271533120705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7262417060070057421655213 2723406397526271533120705)
                      ·
                        rfl

theorem cell23_5303815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_5303815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303815 prefixEnd_5303815 := by exact prefixLift 5303815
  have htrace : WordTrace (prefixWord ++ tailWord_5303815) baseStart_5303815 baseEnd_5303815 := by
    simpa [prefixWord, tailWord_5303815, baseEnd_5303815] using wordTrace_append hprefix tailTrace_5303815
  have hstable : (prefixWord ++ tailWord_5303815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303815).length < 2 ^ (prefixWord ++ tailWord_5303815).sum := by decide
  have hdescent : baseEnd_5303815 < baseStart_5303815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303898 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2]
def baseStart_5303898 : Nat := 118140960795 + 5303898 * 2 ^ 59
def prefixEnd_5303898 : Nat := 4983230072969 + 3 ^ 40 * 5303898 * 2
def baseEnd_5303898 : Nat := 2723449016420594708382823

theorem tailTrace_5303898 : CollatzResearch.WordTrace tailWord_5303898 prefixEnd_5303898 2723449016420594708382823 := by
  unfold tailWord_5303898
  simp only [CollatzResearch.WordTrace]
  refine ⟨48362263134722713626602087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128966035025927236337605565 48362263134722713626602087)
  ·
    refine ⟨72543394702084070439903131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48362263134722713626602087 72543394702084070439903131)
    ·
      refine ⟨108815092053126105659854697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72543394702084070439903131 108815092053126105659854697)
      ·
        refine ⟨81611319039844579244891023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108815092053126105659854697 81611319039844579244891023)
        ·
          refine ⟨122416978559766868867336535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81611319039844579244891023 122416978559766868867336535)
          ·
            refine ⟨183625467839650303301004803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122416978559766868867336535 183625467839650303301004803)
            ·
              refine ⟨275438201759475454951507205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183625467839650303301004803 275438201759475454951507205)
              ·
                refine ⟨51644662829901647803407601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 275438201759475454951507205 51644662829901647803407601)
                ·
                  refine ⟨38733497122426235852555701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51644662829901647803407601 38733497122426235852555701)
                  ·
                    refine ⟨3631265355227459611177097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38733497122426235852555701 3631265355227459611177097)
                    ·
                      refine ⟨2723449016420594708382823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3631265355227459611177097 2723449016420594708382823)
                      ·
                        rfl

theorem cell23_5303898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_5303898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303898 prefixEnd_5303898 := by exact prefixLift 5303898
  have htrace : WordTrace (prefixWord ++ tailWord_5303898) baseStart_5303898 baseEnd_5303898 := by
    simpa [prefixWord, tailWord_5303898, baseEnd_5303898] using wordTrace_append hprefix tailTrace_5303898
  have hstable : (prefixWord ++ tailWord_5303898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303898).length < 2 ^ (prefixWord ++ tailWord_5303898).sum := by decide
  have hdescent : baseEnd_5303898 < baseStart_5303898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303912 : List Nat := [2, 1, 4, 3, 1, 3, 1, 3, 5]
def baseStart_5303912 : Nat := 118140960795 + 5303912 * 2 ^ 59
def prefixEnd_5303912 : Nat := 4983230072969 + 3 ^ 40 * 5303912 * 2
def baseEnd_5303912 : Nat := 302606245016639739289751

theorem tailTrace_5303912 : CollatzResearch.WordTrace tailWord_5303912 prefixEnd_5303912 302606245016639739289751 := by
  unfold tailWord_5303912
  simp only [CollatzResearch.WordTrace]
  refine ⟨96724781580420067448708995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128966375440560089931611993 96724781580420067448708995)
  ·
    refine ⟨145087172370630101173063493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96724781580420067448708995 145087172370630101173063493)
    ·
      refine ⟨27203844819493143969949405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145087172370630101173063493 27203844819493143969949405)
      ·
        refine ⟨10201441807309928988731027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27203844819493143969949405 10201441807309928988731027)
        ·
          refine ⟨15302162710964893483096541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10201441807309928988731027 15302162710964893483096541)
          ·
            refine ⟨5738311016611835056161203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15302162710964893483096541 5738311016611835056161203)
            ·
              refine ⟨8607466524917752584241805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5738311016611835056161203 8607466524917752584241805)
              ·
                refine ⟨3227799946844157219090677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8607466524917752584241805 3227799946844157219090677)
                ·
                  refine ⟨302606245016639739289751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3227799946844157219090677 302606245016639739289751)
                  ·
                    rfl

theorem cell23_5303912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 3, 5].length) (baseStart_5303912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303912 prefixEnd_5303912 := by exact prefixLift 5303912
  have htrace : WordTrace (prefixWord ++ tailWord_5303912) baseStart_5303912 baseEnd_5303912 := by
    simpa [prefixWord, tailWord_5303912, baseEnd_5303912] using wordTrace_append hprefix tailTrace_5303912
  have hstable : (prefixWord ++ tailWord_5303912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303912).length < 2 ^ (prefixWord ++ tailWord_5303912).sum := by decide
  have hdescent : baseEnd_5303912 < baseStart_5303912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303925 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 2, 5]
def baseStart_5303925 : Nat := 118140960795 + 5303925 * 2 ^ 59
def prefixEnd_5303925 : Nat := 4983230072969 + 3 ^ 40 * 5303925 * 2
def baseEnd_5303925 : Nat := 907820960132755367581733

theorem tailTrace_5303925 : CollatzResearch.WordTrace tailWord_5303925 prefixEnd_5303925 907820960132755367581733 := by
  unfold tailWord_5303925
  simp only [CollatzResearch.WordTrace]
  refine ⟨193450037309793038117641229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128966691539862025411760819 193450037309793038117641229)
  ·
    refine ⟨72543763991172389294115461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193450037309793038117641229 72543763991172389294115461)
    ·
      refine ⟨13601955748344822992646649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72543763991172389294115461 13601955748344822992646649)
      ·
        refine ⟨10201466811258617244484987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13601955748344822992646649 10201466811258617244484987)
        ·
          refine ⟨15302200216887925866727481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10201466811258617244484987 15302200216887925866727481)
          ·
            refine ⟨11476650162665944400045611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15302200216887925866727481 11476650162665944400045611)
            ·
              refine ⟨17214975243998916600068417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11476650162665944400045611 17214975243998916600068417)
              ·
                refine ⟨12911231432999187450051313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17214975243998916600068417 12911231432999187450051313)
                ·
                  refine ⟨9683423574749390587538485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12911231432999187450051313 9683423574749390587538485)
                  ·
                    refine ⟨907820960132755367581733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9683423574749390587538485 907820960132755367581733)
                    ·
                      rfl

theorem cell23_5303925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_5303925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303925 prefixEnd_5303925 := by exact prefixLift 5303925
  have htrace : WordTrace (prefixWord ++ tailWord_5303925) baseStart_5303925 baseEnd_5303925 := by
    simpa [prefixWord, tailWord_5303925, baseEnd_5303925] using wordTrace_append hprefix tailTrace_5303925
  have hstable : (prefixWord ++ tailWord_5303925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303925).length < 2 ^ (prefixWord ++ tailWord_5303925).sum := by decide
  have hdescent : baseEnd_5303925 < baseStart_5303925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303948 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 4, 2, 3]
def baseStart_5303948 : Nat := 118140960795 + 5303948 * 2 ^ 59
def prefixEnd_5303948 : Nat := 4983230072969 + 3 ^ 40 * 5303948 * 2
def baseEnd_5303948 : Nat := 2723474690453319512757593

theorem tailTrace_5303948 : CollatzResearch.WordTrace tailWord_5303948 prefixEnd_5303948 2723474690453319512757593 := by
  unfold tailWord_5303948
  simp only [CollatzResearch.WordTrace]
  refine ⟨96725438094354856522864249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128967250792473142030485665 96725438094354856522864249)
  ·
    refine ⟨72544078570766142392148187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96725438094354856522864249 72544078570766142392148187)
    ·
      refine ⟨108816117856149213588222281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72544078570766142392148187 108816117856149213588222281)
      ·
        refine ⟨81612088392111910191166711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108816117856149213588222281 81612088392111910191166711)
        ·
          refine ⟨122418132588167865286750067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81612088392111910191166711 122418132588167865286750067)
          ·
            refine ⟨183627198882251797930125101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122418132588167865286750067 183627198882251797930125101)
            ·
              refine ⟨68860199580844424223796913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183627198882251797930125101 68860199580844424223796913)
              ·
                refine ⟨51645149685633318167847685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68860199580844424223796913 51645149685633318167847685)
                ·
                  refine ⟨9683465566056247156471441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51645149685633318167847685 9683465566056247156471441)
                  ·
                    refine ⟨7262599174542185367353581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9683465566056247156471441 7262599174542185367353581)
                    ·
                      refine ⟨2723474690453319512757593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7262599174542185367353581 2723474690453319512757593)
                      ·
                        rfl

theorem cell23_5303948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_5303948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303948 prefixEnd_5303948 := by exact prefixLift 5303948
  have htrace : WordTrace (prefixWord ++ tailWord_5303948) baseStart_5303948 baseEnd_5303948 := by
    simpa [prefixWord, tailWord_5303948, baseEnd_5303948] using wordTrace_append hprefix tailTrace_5303948
  have hstable : (prefixWord ++ tailWord_5303948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303948).length < 2 ^ (prefixWord ++ tailWord_5303948).sum := by decide
  have hdescent : baseEnd_5303948 < baseStart_5303948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5303989 : List Nat := [1, 3, 3, 3, 2, 1, 1, 4, 1, 4]
def baseStart_5303989 : Nat := 118140960795 + 5303989 * 2 ^ 59
def prefixEnd_5303989 : Nat := 4983230072969 + 3 ^ 40 * 5303989 * 2
def baseEnd_5303989 : Nat := 907831914386717950781635

theorem tailTrace_5303989 : CollatzResearch.WordTrace tailWord_5303989 prefixEnd_5303989 907831914386717950781635 := by
  unfold tailWord_5303989
  simp only [CollatzResearch.WordTrace]
  refine ⟨193452371581561177047971021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128968247721040784698647347 193452371581561177047971021)
  ·
    refine ⟨72544639343085441392989133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193452371581561177047971021 72544639343085441392989133)
    ·
      refine ⟨27204239753657040522370925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72544639343085441392989133 27204239753657040522370925)
      ·
        refine ⟨10201589907621390195889097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27204239753657040522370925 10201589907621390195889097)
        ·
          refine ⟨7651192430716042646916823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10201589907621390195889097 7651192430716042646916823)
          ·
            refine ⟨11476788646074063970375235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7651192430716042646916823 11476788646074063970375235)
            ·
              refine ⟨17215182969111095955562853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11476788646074063970375235 17215182969111095955562853)
              ·
                refine ⟨3227846806708330491668035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17215182969111095955562853 3227846806708330491668035)
                ·
                  refine ⟨4841770210062495737502053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3227846806708330491668035 4841770210062495737502053)
                  ·
                    refine ⟨907831914386717950781635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4841770210062495737502053 907831914386717950781635)
                    ·
                      rfl

theorem cell23_5303989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_5303989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5303989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5303989 prefixEnd_5303989 := by exact prefixLift 5303989
  have htrace : WordTrace (prefixWord ++ tailWord_5303989) baseStart_5303989 baseEnd_5303989 := by
    simpa [prefixWord, tailWord_5303989, baseEnd_5303989] using wordTrace_append hprefix tailTrace_5303989
  have hstable : (prefixWord ++ tailWord_5303989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5303989).length < 2 ^ (prefixWord ++ tailWord_5303989).sum := by decide
  have hdescent : baseEnd_5303989 < baseStart_5303989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5303989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304065 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_5304065 : Nat := 118140960795 + 5304065 * 2 ^ 59
def prefixEnd_5304065 : Nat := 4983230072969 + 3 ^ 40 * 5304065 * 2
def baseEnd_5304065 : Nat := 2723534767689895554994555

theorem tailTrace_5304065 : CollatzResearch.WordTrace tailWord_5304065 prefixEnd_5304065 2723534767689895554994555 := by
  unfold tailWord_5304065
  simp only [CollatzResearch.WordTrace]
  refine ⟨193455143529285842027737649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128970095686190561351825099 193455143529285842027737649)
  ·
    refine ⟨145091357646964381520803237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193455143529285842027737649 145091357646964381520803237)
    ·
      refine ⟨27204629558805821535150607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145091357646964381520803237 27204629558805821535150607)
      ·
        refine ⟨40806944338208732302725911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27204629558805821535150607 40806944338208732302725911)
        ·
          refine ⟨61210416507313098454088867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40806944338208732302725911 61210416507313098454088867)
          ·
            refine ⟨91815624760969647681133301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61210416507313098454088867 91815624760969647681133301)
            ·
              refine ⟨8607714821340904470106247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91815624760969647681133301 8607714821340904470106247)
              ·
                refine ⟨12911572232011356705159371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8607714821340904470106247 12911572232011356705159371)
                ·
                  refine ⟨19367358348017035057739057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12911572232011356705159371 19367358348017035057739057)
                  ·
                    refine ⟨14525518761012776293304293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19367358348017035057739057 14525518761012776293304293)
                    ·
                      refine ⟨2723534767689895554994555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14525518761012776293304293 2723534767689895554994555)
                      ·
                        rfl

theorem cell23_5304065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_5304065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304065 prefixEnd_5304065 := by exact prefixLift 5304065
  have htrace : WordTrace (prefixWord ++ tailWord_5304065) baseStart_5304065 baseEnd_5304065 := by
    simpa [prefixWord, tailWord_5304065, baseEnd_5304065] using wordTrace_append hprefix tailTrace_5304065
  have hstable : (prefixWord ++ tailWord_5304065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304065).length < 2 ^ (prefixWord ++ tailWord_5304065).sum := by decide
  have hdescent : baseEnd_5304065 < baseStart_5304065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304072 : List Nat := [2, 1, 3, 2, 2, 1, 4, 2, 1, 2, 3]
def baseStart_5304072 : Nat := 118140960795 + 5304072 * 2 ^ 59
def prefixEnd_5304072 : Nat := 4983230072969 + 3 ^ 40 * 5304072 * 2
def baseEnd_5304072 : Nat := 2723538362054477027607023

theorem tailTrace_5304072 : CollatzResearch.WordTrace tailWord_5304072 prefixEnd_5304072 2723538362054477027607023 := by
  unfold tailWord_5304072
  simp only [CollatzResearch.WordTrace]
  refine ⟨96727699420130241111621235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128970265893506988148828313 96727699420130241111621235)
  ·
    refine ⟨145091549130195361667431853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96727699420130241111621235 145091549130195361667431853)
    ·
      refine ⟨54409330923823260625286945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145091549130195361667431853 54409330923823260625286945)
      ·
        refine ⟨40806998192867445468965209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54409330923823260625286945 40806998192867445468965209)
        ·
          refine ⟨30605248644650584101723907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40806998192867445468965209 30605248644650584101723907)
          ·
            refine ⟨45907872966975876152585861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30605248644650584101723907 45907872966975876152585861)
            ·
              refine ⟨8607726181307976778609849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45907872966975876152585861 8607726181307976778609849)
              ·
                refine ⟨6455794635980982583957387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8607726181307976778609849 6455794635980982583957387)
                ·
                  refine ⟨9683691953971473875936081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6455794635980982583957387 9683691953971473875936081)
                  ·
                    refine ⟨7262768965478605406952061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9683691953971473875936081 7262768965478605406952061)
                    ·
                      refine ⟨2723538362054477027607023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7262768965478605406952061 2723538362054477027607023)
                      ·
                        rfl

theorem cell23_5304072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_5304072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304072 prefixEnd_5304072 := by exact prefixLift 5304072
  have htrace : WordTrace (prefixWord ++ tailWord_5304072) baseStart_5304072 baseEnd_5304072 := by
    simpa [prefixWord, tailWord_5304072, baseEnd_5304072] using wordTrace_append hprefix tailTrace_5304072
  have hstable : (prefixWord ++ tailWord_5304072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304072).length < 2 ^ (prefixWord ++ tailWord_5304072).sum := by decide
  have hdescent : baseEnd_5304072 < baseStart_5304072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304145 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 2, 1, 5]
def baseStart_5304145 : Nat := 118140960795 + 5304145 * 2 ^ 59
def prefixEnd_5304145 : Nat := 4983230072969 + 3 ^ 40 * 5304145 * 2
def baseEnd_5304145 : Nat := 2723575846142255241994187

theorem tailTrace_5304145 : CollatzResearch.WordTrace tailWord_5304145 prefixEnd_5304145 2723575846142255241994187 := by
  unfold tailWord_5304145
  simp only [CollatzResearch.WordTrace]
  refine ⟨193458061368996015690649889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128972040912664010460433259 193458061368996015690649889)
  ·
    refine ⟨145093546026747011767987417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193458061368996015690649889 145093546026747011767987417)
    ·
      refine ⟨108820159520060258825990563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145093546026747011767987417 108820159520060258825990563)
      ·
        refine ⟨163230239280090388238985845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108820159520060258825990563 163230239280090388238985845)
        ·
          refine ⟨15302834932508473897404923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163230239280090388238985845 15302834932508473897404923)
          ·
            refine ⟨22954252398762710846107385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15302834932508473897404923 22954252398762710846107385)
            ·
              refine ⟨17215689299072033134580539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22954252398762710846107385 17215689299072033134580539)
              ·
                refine ⟨25823533948608049701870809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17215689299072033134580539 25823533948608049701870809)
                ·
                  refine ⟨19367650461456037276403107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25823533948608049701870809 19367650461456037276403107)
                  ·
                    refine ⟨29051475692184055914604661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19367650461456037276403107 29051475692184055914604661)
                    ·
                      refine ⟨2723575846142255241994187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29051475692184055914604661 2723575846142255241994187)
                      ·
                        rfl

theorem cell23_5304145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_5304145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304145 prefixEnd_5304145 := by exact prefixLift 5304145
  have htrace : WordTrace (prefixWord ++ tailWord_5304145) baseStart_5304145 baseEnd_5304145 := by
    simpa [prefixWord, tailWord_5304145, baseEnd_5304145] using wordTrace_append hprefix tailTrace_5304145
  have hstable : (prefixWord ++ tailWord_5304145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304145).length < 2 ^ (prefixWord ++ tailWord_5304145).sum := by decide
  have hdescent : baseEnd_5304145 < baseStart_5304145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304146 : List Nat := [3, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2]
def baseStart_5304146 : Nat := 118140960795 + 5304146 * 2 ^ 59
def prefixEnd_5304146 : Nat := 4983230072969 + 3 ^ 40 * 5304146 * 2
def baseEnd_5304146 : Nat := 2723576359622909738081683

theorem tailTrace_5304146 : CollatzResearch.WordTrace tailWord_5304146 prefixEnd_5304146 2723576359622909738081683 := by
  unfold tailWord_5304146
  simp only [CollatzResearch.WordTrace]
  refine ⟨48364524460498098215359073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128972065227994928574290861 48364524460498098215359073)
  ·
    refine ⟨36273393345373573661519305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48364524460498098215359073 36273393345373573661519305)
    ·
      refine ⟨27205045009030180246139479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36273393345373573661519305 27205045009030180246139479)
      ·
        refine ⟨40807567513545270369209219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27205045009030180246139479 40807567513545270369209219)
        ·
          refine ⟨61211351270317905553813829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40807567513545270369209219 61211351270317905553813829)
          ·
            refine ⟨11477128363184607291340093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61211351270317905553813829 11477128363184607291340093)
            ·
              refine ⟨4303923136194227734252535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11477128363184607291340093 4303923136194227734252535)
              ·
                refine ⟨6455884704291341601378803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303923136194227734252535 6455884704291341601378803)
                ·
                  refine ⟨9683827056437012402068205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6455884704291341601378803 9683827056437012402068205)
                  ·
                    refine ⟨3631435146163879650775577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9683827056437012402068205 3631435146163879650775577)
                    ·
                      refine ⟨2723576359622909738081683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3631435146163879650775577 2723576359622909738081683)
                      ·
                        rfl

theorem cell23_5304146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_5304146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304146 prefixEnd_5304146 := by exact prefixLift 5304146
  have htrace : WordTrace (prefixWord ++ tailWord_5304146) baseStart_5304146 baseEnd_5304146 := by
    simpa [prefixWord, tailWord_5304146, baseEnd_5304146] using wordTrace_append hprefix tailTrace_5304146
  have hstable : (prefixWord ++ tailWord_5304146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304146).length < 2 ^ (prefixWord ++ tailWord_5304146).sum := by decide
  have hdescent : baseEnd_5304146 < baseStart_5304146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304159 : List Nat := [1, 1, 2, 3, 1, 4, 1, 4, 2, 2, 2]
def baseStart_5304159 : Nat := 118140960795 + 5304159 * 2 ^ 59
def prefixEnd_5304159 : Nat := 4983230072969 + 3 ^ 40 * 5304159 * 2
def baseEnd_5304159 : Nat := 2723583034871418187219123

theorem tailTrace_5304159 : CollatzResearch.WordTrace tailWord_5304159 prefixEnd_5304159 2723583034871418187219123 := by
  unfold tailWord_5304159
  simp only [CollatzResearch.WordTrace]
  refine ⟨193458571990945296081659531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128972381327296864054439687 193458571990945296081659531)
  ·
    refine ⟨290187857986417944122489297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193458571990945296081659531 290187857986417944122489297)
    ·
      refine ⟨217640893489813458091866973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290187857986417944122489297 217640893489813458091866973)
      ·
        refine ⟨81615335058680046784450115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217640893489813458091866973 81615335058680046784450115)
        ·
          refine ⟨122423002588020070176675173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81615335058680046784450115 122423002588020070176675173)
          ·
            refine ⟨22954312985253763158126595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122423002588020070176675173 22954312985253763158126595)
            ·
              refine ⟨34431469477880644737189893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22954312985253763158126595 34431469477880644737189893)
              ·
                refine ⟨6455900527102620888223105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34431469477880644737189893 6455900527102620888223105)
                ·
                  refine ⟨4841925395326965666167329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6455900527102620888223105 4841925395326965666167329)
                  ·
                    refine ⟨3631444046495224249625497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4841925395326965666167329 3631444046495224249625497)
                    ·
                      refine ⟨2723583034871418187219123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3631444046495224249625497 2723583034871418187219123)
                      ·
                        rfl

theorem cell23_5304159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_5304159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304159 prefixEnd_5304159 := by exact prefixLift 5304159
  have htrace : WordTrace (prefixWord ++ tailWord_5304159) baseStart_5304159 baseEnd_5304159 := by
    simpa [prefixWord, tailWord_5304159, baseEnd_5304159] using wordTrace_append hprefix tailTrace_5304159
  have hstable : (prefixWord ++ tailWord_5304159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304159).length < 2 ^ (prefixWord ++ tailWord_5304159).sum := by decide
  have hdescent : baseEnd_5304159 < baseStart_5304159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304162 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_5304162 : Nat := 118140960795 + 5304162 * 2 ^ 59
def prefixEnd_5304162 : Nat := 4983230072969 + 3 ^ 40 * 5304162 * 2
def baseEnd_5304162 : Nat := 2723584575313381675481609

theorem tailTrace_5304162 : CollatzResearch.WordTrace tailWord_5304162 prefixEnd_5304162 2723584575313381675481609 := by
  unfold tailWord_5304162
  simp only [CollatzResearch.WordTrace]
  refine ⟨48364670352483606898504685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128972454273289618396012493 48364670352483606898504685)
  ·
    refine ⟨18136751382181352586939257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48364670352483606898504685 18136751382181352586939257)
    ·
      refine ⟨13602563536636014440204443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18136751382181352586939257 13602563536636014440204443)
      ·
        refine ⟨20403845304954021660306665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13602563536636014440204443 20403845304954021660306665)
        ·
          refine ⟨15302883978715516245229999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20403845304954021660306665 15302883978715516245229999)
          ·
            refine ⟨22954325968073274367844999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15302883978715516245229999 22954325968073274367844999)
            ·
              refine ⟨34431488952109911551767499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22954325968073274367844999 34431488952109911551767499)
              ·
                refine ⟨51647233428164867327651249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34431488952109911551767499 51647233428164867327651249)
                ·
                  refine ⟨38735425071123650495738437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51647233428164867327651249 38735425071123650495738437)
                  ·
                    refine ⟨7262892200835684467950957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38735425071123650495738437 7262892200835684467950957)
                    ·
                      refine ⟨2723584575313381675481609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7262892200835684467950957 2723584575313381675481609)
                      ·
                        rfl

theorem cell23_5304162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_5304162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304162 prefixEnd_5304162 := by exact prefixLift 5304162
  have htrace : WordTrace (prefixWord ++ tailWord_5304162) baseStart_5304162 baseEnd_5304162 := by
    simpa [prefixWord, tailWord_5304162, baseEnd_5304162] using wordTrace_append hprefix tailTrace_5304162
  have hstable : (prefixWord ++ tailWord_5304162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304162).length < 2 ^ (prefixWord ++ tailWord_5304162).sum := by decide
  have hdescent : baseEnd_5304162 < baseStart_5304162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304195 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 1, 7]
def baseStart_5304195 : Nat := 118140960795 + 5304195 * 2 ^ 59
def prefixEnd_5304195 : Nat := 4983230072969 + 3 ^ 40 * 5304195 * 2
def baseEnd_5304195 : Nat := 907867173391660015456319

theorem tailTrace_5304195 : CollatzResearch.WordTrace tailWord_5304195 prefixEnd_5304195 907867173391660015456319 := by
  unfold tailWord_5304195
  simp only [CollatzResearch.WordTrace]
  refine ⟨193459885018814874229970039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128973256679209916153313359 193459885018814874229970039)
  ·
    refine ⟨290189827528222311344955059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193459885018814874229970039 290189827528222311344955059)
    ·
      refine ⟨435284741292333467017432589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290189827528222311344955059 435284741292333467017432589)
      ·
        refine ⟨163231777984625050131537221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435284741292333467017432589 163231777984625050131537221)
        ·
          refine ⟨30605958372117196899663229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163231777984625050131537221 30605958372117196899663229)
          ·
            refine ⟨11477234389543948837373711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30605958372117196899663229 11477234389543948837373711)
            ·
              refine ⟨17215851584315923256060567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11477234389543948837373711 17215851584315923256060567)
              ·
                refine ⟨25823777376473884884090851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17215851584315923256060567 25823777376473884884090851)
                ·
                  refine ⟨38735666064710827326136277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25823777376473884884090851 38735666064710827326136277)
                  ·
                    refine ⟨907867173391660015456319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38735666064710827326136277 907867173391660015456319)
                    ·
                      rfl

theorem cell23_5304195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 7].length) (baseStart_5304195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304195 prefixEnd_5304195 := by exact prefixLift 5304195
  have htrace : WordTrace (prefixWord ++ tailWord_5304195) baseStart_5304195 baseEnd_5304195 := by
    simpa [prefixWord, tailWord_5304195, baseEnd_5304195] using wordTrace_append hprefix tailTrace_5304195
  have hstable : (prefixWord ++ tailWord_5304195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304195).length < 2 ^ (prefixWord ++ tailWord_5304195).sum := by decide
  have hdescent : baseEnd_5304195 < baseStart_5304195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304199 : List Nat := [1, 1, 4, 2, 4, 1, 2, 3, 5]
def baseStart_5304199 : Nat := 118140960795 + 5304199 * 2 ^ 59
def prefixEnd_5304199 : Nat := 4983230072969 + 3 ^ 40 * 5304199 * 2
def baseEnd_5304199 : Nat := 302622619344177558968771

theorem tailTrace_5304199 : CollatzResearch.WordTrace tailWord_5304199 prefixEnd_5304199 302622619344177558968771 := by
  unfold tailWord_5304199
  simp only [CollatzResearch.WordTrace]
  refine ⟨193460030910800382913115651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128973353940533588608743767 193460030910800382913115651)
  ·
    refine ⟨290190046366200574369673477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193460030910800382913115651 290190046366200574369673477)
    ·
      refine ⟨54410633693662607694313777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290190046366200574369673477 54410633693662607694313777)
      ·
        refine ⟨40807975270246955770735333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54410633693662607694313777 40807975270246955770735333)
        ·
          refine ⟨7651495363171304207012875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40807975270246955770735333 7651495363171304207012875)
          ·
            refine ⟨11477243044756956310519313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7651495363171304207012875 11477243044756956310519313)
            ·
              refine ⟨8607932283567717232889485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11477243044756956310519313 8607932283567717232889485)
              ·
                refine ⟨3227974606337893962333557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8607932283567717232889485 3227974606337893962333557)
                ·
                  refine ⟨302622619344177558968771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3227974606337893962333557 302622619344177558968771)
                  ·
                    rfl

theorem cell23_5304199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 5].length) (baseStart_5304199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304199 prefixEnd_5304199 := by exact prefixLift 5304199
  have htrace : WordTrace (prefixWord ++ tailWord_5304199) baseStart_5304199 baseEnd_5304199 := by
    simpa [prefixWord, tailWord_5304199, baseEnd_5304199] using wordTrace_append hprefix tailTrace_5304199
  have hstable : (prefixWord ++ tailWord_5304199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304199).length < 2 ^ (prefixWord ++ tailWord_5304199).sum := by decide
  have hdescent : baseEnd_5304199 < baseStart_5304199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304265 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 1, 7, 3]
def baseStart_5304265 : Nat := 118140960795 + 5304265 * 2 ^ 59
def prefixEnd_5304265 : Nat := 4983230072969 + 3 ^ 40 * 5304265 * 2
def baseEnd_5304265 : Nat := 2723637463820794772493635

theorem tailTrace_5304265 : CollatzResearch.WordTrace tailWord_5304265 prefixEnd_5304265 2723637463820794772493635 := by
  unfold tailWord_5304265
  simp only [CollatzResearch.WordTrace]
  refine ⟨193462438128561276185018249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128974958752374184123345499 193462438128561276185018249)
  ·
    refine ⟨145096828596420957138763687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193462438128561276185018249 145096828596420957138763687)
    ·
      refine ⟨217645242894631435708145531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145096828596420957138763687 217645242894631435708145531)
      ·
        refine ⟨326467864341947153562218297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217645242894631435708145531 326467864341947153562218297)
        ·
          refine ⟨244850898256460365171663723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326467864341947153562218297 244850898256460365171663723)
          ·
            refine ⟨367276347384690547757495585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244850898256460365171663723 367276347384690547757495585)
            ·
              refine ⟨275457260538517910818121689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367276347384690547757495585 275457260538517910818121689)
              ·
                refine ⟨206592945403888433113591267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275457260538517910818121689 206592945403888433113591267)
                ·
                  refine ⟨309889418105832649670386901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206592945403888433113591267 309889418105832649670386901)
                  ·
                    refine ⟨7263033236855452726649693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 309889418105832649670386901 7263033236855452726649693)
                    ·
                      refine ⟨2723637463820794772493635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7263033236855452726649693 2723637463820794772493635)
                      ·
                        rfl

theorem cell23_5304265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 7, 3].length) (baseStart_5304265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304265 prefixEnd_5304265 := by exact prefixLift 5304265
  have htrace : WordTrace (prefixWord ++ tailWord_5304265) baseStart_5304265 baseEnd_5304265 := by
    simpa [prefixWord, tailWord_5304265, baseEnd_5304265] using wordTrace_append hprefix tailTrace_5304265
  have hstable : (prefixWord ++ tailWord_5304265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304265).length < 2 ^ (prefixWord ++ tailWord_5304265).sum := by decide
  have hdescent : baseEnd_5304265 < baseStart_5304265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304315 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 3, 6]
def baseStart_5304315 : Nat := 118140960795 + 5304315 * 2 ^ 59
def prefixEnd_5304315 : Nat := 4983230072969 + 3 ^ 40 * 5304315 * 2
def baseEnd_5304315 : Nat := 907887712617839858956135

theorem tailTrace_5304315 : CollatzResearch.WordTrace tailWord_5304315 prefixEnd_5304315 907887712617839858956135 := by
  unfold tailWord_5304315
  simp only [CollatzResearch.WordTrace]
  refine ⟨193464261778380134724338399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128976174518920089816225599 193464261778380134724338399)
  ·
    refine ⟨290196392667570202086507599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193464261778380134724338399 290196392667570202086507599)
    ·
      refine ⟨435294589001355303129761399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290196392667570202086507599 435294589001355303129761399)
      ·
        refine ⟨652941883502032954694642099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435294589001355303129761399 652941883502032954694642099)
        ·
          refine ⟨979412825253049432041963149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652941883502032954694642099 979412825253049432041963149)
          ·
            refine ⟨367279809469893537015736181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 979412825253049432041963149 367279809469893537015736181)
            ·
              refine ⟨34432482137802519095225267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 367279809469893537015736181 34432482137802519095225267)
              ·
                refine ⟨51648723206703778642837901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34432482137802519095225267 51648723206703778642837901)
                ·
                  refine ⟨19368271202513916991064213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51648723206703778642837901 19368271202513916991064213)
                  ·
                    refine ⟨907887712617839858956135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19368271202513916991064213 907887712617839858956135)
                    ·
                      rfl

theorem cell23_5304315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 6].length) (baseStart_5304315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304315 prefixEnd_5304315 := by exact prefixLift 5304315
  have htrace : WordTrace (prefixWord ++ tailWord_5304315) baseStart_5304315 baseEnd_5304315 := by
    simpa [prefixWord, tailWord_5304315, baseEnd_5304315] using wordTrace_append hprefix tailTrace_5304315
  have hstable : (prefixWord ++ tailWord_5304315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304315).length < 2 ^ (prefixWord ++ tailWord_5304315).sum := by decide
  have hdescent : baseEnd_5304315 < baseStart_5304315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304316 : List Nat := [2, 2, 2, 1, 2, 2, 2, 5, 1, 1, 3]
def baseStart_5304316 : Nat := 118140960795 + 5304316 * 2 ^ 59
def prefixEnd_5304316 : Nat := 4983230072969 + 3 ^ 40 * 5304316 * 2
def baseEnd_5304316 : Nat := 2723663651334174072955901

theorem tailTrace_5304316 : CollatzResearch.WordTrace tailWord_5304316 prefixEnd_5304316 2723663651334174072955901 := by
  unfold tailWord_5304316
  simp only [CollatzResearch.WordTrace]
  refine ⟨96732149125688255947562401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128976198834251007930083201 96732149125688255947562401)
  ·
    refine ⟨72549111844266191960671801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96732149125688255947562401 72549111844266191960671801)
    ·
      refine ⟨54411833883199643970503851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72549111844266191960671801 54411833883199643970503851)
      ·
        refine ⟨81617750824799465955755777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54411833883199643970503851 81617750824799465955755777)
        ·
          refine ⟨61213313118599599466816833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81617750824799465955755777 61213313118599599466816833)
          ·
            refine ⟨45909984838949699600112625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61213313118599599466816833 45909984838949699600112625)
            ·
              refine ⟨34432488629212274700084469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45909984838949699600112625 34432488629212274700084469)
              ·
                refine ⟨3228045808988650753132919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34432488629212274700084469 3228045808988650753132919)
                ·
                  refine ⟨4842068713482976129699379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228045808988650753132919 4842068713482976129699379)
                  ·
                    refine ⟨7263103070224464194549069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4842068713482976129699379 7263103070224464194549069)
                    ·
                      refine ⟨2723663651334174072955901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7263103070224464194549069 2723663651334174072955901)
                      ·
                        rfl

theorem cell23_5304316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 1, 1, 3].length) (baseStart_5304316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304316 prefixEnd_5304316 := by exact prefixLift 5304316
  have htrace : WordTrace (prefixWord ++ tailWord_5304316) baseStart_5304316 baseEnd_5304316 := by
    simpa [prefixWord, tailWord_5304316, baseEnd_5304316] using wordTrace_append hprefix tailTrace_5304316
  have hstable : (prefixWord ++ tailWord_5304316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304316).length < 2 ^ (prefixWord ++ tailWord_5304316).sum := by decide
  have hdescent : baseEnd_5304316 < baseStart_5304316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304335 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 4]
def baseStart_5304335 : Nat := 118140960795 + 5304335 * 2 ^ 59
def prefixEnd_5304335 : Nat := 4983230072969 + 3 ^ 40 * 5304335 * 2
def baseEnd_5304335 : Nat := 2723673407466609498618313

theorem tailTrace_5304335 : CollatzResearch.WordTrace tailWord_5304335 prefixEnd_5304335 2723673407466609498618313 := by
  unfold tailWord_5304335
  simp only [CollatzResearch.WordTrace]
  refine ⟨193464991238307678140066459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128976660825538452093377639 193464991238307678140066459)
  ·
    refine ⟨290197486857461517210099689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193464991238307678140066459 290197486857461517210099689)
    ·
      refine ⟨217648115143096137907574767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290197486857461517210099689 217648115143096137907574767)
      ·
        refine ⟨326472172714644206861362151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217648115143096137907574767 326472172714644206861362151)
        ·
          refine ⟨489708259071966310292043227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326472172714644206861362151 489708259071966310292043227)
          ·
            refine ⟨734562388607949465438064841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489708259071966310292043227 734562388607949465438064841)
            ·
              refine ⟨550921791455962099078548631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734562388607949465438064841 550921791455962099078548631)
              ·
                refine ⟨826382687183943148617822947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550921791455962099078548631 826382687183943148617822947)
                ·
                  refine ⟨1239574030775914722926734421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 826382687183943148617822947 1239574030775914722926734421)
                  ·
                    refine ⟨14526258173155250659297669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1239574030775914722926734421 14526258173155250659297669)
                    ·
                      refine ⟨2723673407466609498618313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14526258173155250659297669 2723673407466609498618313)
                      ·
                        rfl

theorem cell23_5304335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_5304335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304335 prefixEnd_5304335 := by exact prefixLift 5304335
  have htrace : WordTrace (prefixWord ++ tailWord_5304335) baseStart_5304335 baseEnd_5304335 := by
    simpa [prefixWord, tailWord_5304335, baseEnd_5304335] using wordTrace_append hprefix tailTrace_5304335
  have hstable : (prefixWord ++ tailWord_5304335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304335).length < 2 ^ (prefixWord ++ tailWord_5304335).sum := by decide
  have hdescent : baseEnd_5304335 < baseStart_5304335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304349 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 1, 6]
def baseStart_5304349 : Nat := 118140960795 + 5304349 * 2 ^ 59
def prefixEnd_5304349 : Nat := 4983230072969 + 3 ^ 40 * 5304349 * 2
def baseEnd_5304349 : Nat := 907893532065257481281083

theorem tailTrace_5304349 : CollatzResearch.WordTrace tailWord_5304349 prefixEnd_5304349 907893532065257481281083 := by
  unfold tailWord_5304349
  simp only [CollatzResearch.WordTrace]
  refine ⟨193465501860256958531076101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128977001240171305687384067 193465501860256958531076101)
  ·
    refine ⟨36274781598798179724576769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193465501860256958531076101 36274781598798179724576769)
    ·
      refine ⟨27206086199098634793432577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36274781598798179724576769 27206086199098634793432577)
      ·
        refine ⟨20404564649323976095074433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27206086199098634793432577 20404564649323976095074433)
        ·
          refine ⟨15303423486992982071305825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20404564649323976095074433 15303423486992982071305825)
          ·
            refine ⟨11477567615244736553479369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15303423486992982071305825 11477567615244736553479369)
            ·
              refine ⟨8608175711433552415109527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11477567615244736553479369 8608175711433552415109527)
              ·
                refine ⟨12912263567150328622664291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8608175711433552415109527 12912263567150328622664291)
                ·
                  refine ⟨19368395350725492933996437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12912263567150328622664291 19368395350725492933996437)
                  ·
                    refine ⟨907893532065257481281083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19368395350725492933996437 907893532065257481281083)
                    ·
                      rfl

theorem cell23_5304349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_5304349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304349 prefixEnd_5304349 := by exact prefixLift 5304349
  have htrace : WordTrace (prefixWord ++ tailWord_5304349) baseStart_5304349 baseEnd_5304349 := by
    simpa [prefixWord, tailWord_5304349, baseEnd_5304349] using wordTrace_append hprefix tailTrace_5304349
  have hstable : (prefixWord ++ tailWord_5304349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304349).length < 2 ^ (prefixWord ++ tailWord_5304349).sum := by decide
  have hdescent : baseEnd_5304349 < baseStart_5304349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304360 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_5304360 : Nat := 118140960795 + 5304360 * 2 ^ 59
def prefixEnd_5304360 : Nat := 4983230072969 + 3 ^ 40 * 5304360 * 2
def baseEnd_5304360 : Nat := 2723686244482971900805699

theorem tailTrace_5304360 : CollatzResearch.WordTrace tailWord_5304360 prefixEnd_5304360 2723686244482971900805699 := by
  unfold tailWord_5304360
  simp only [CollatzResearch.WordTrace]
  refine ⟨96732951531608553704863267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128977268708811404939817689 96732951531608553704863267)
  ·
    refine ⟨145099427297412830557294901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96732951531608553704863267 145099427297412830557294901)
    ·
      refine ⟨13603071309132452864746397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145099427297412830557294901 13603071309132452864746397)
      ·
        refine ⟨5101151740924669824279899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13603071309132452864746397 5101151740924669824279899)
        ·
          refine ⟨7651727611387004736419849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5101151740924669824279899 7651727611387004736419849)
          ·
            refine ⟨5738795708540253552314887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7651727611387004736419849 5738795708540253552314887)
            ·
              refine ⟨8608193562810380328472331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5738795708540253552314887 8608193562810380328472331)
              ·
                refine ⟨12912290344215570492708497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8608193562810380328472331 12912290344215570492708497)
                ·
                  refine ⟨9684217758161677869531373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12912290344215570492708497 9684217758161677869531373)
                  ·
                    refine ⟨3631581659310629201074265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9684217758161677869531373 3631581659310629201074265)
                    ·
                      refine ⟨2723686244482971900805699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3631581659310629201074265 2723686244482971900805699)
                      ·
                        rfl

theorem cell23_5304360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_5304360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304360 prefixEnd_5304360 := by exact prefixLift 5304360
  have htrace : WordTrace (prefixWord ++ tailWord_5304360) baseStart_5304360 baseEnd_5304360 := by
    simpa [prefixWord, tailWord_5304360, baseEnd_5304360] using wordTrace_append hprefix tailTrace_5304360
  have hstable : (prefixWord ++ tailWord_5304360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304360).length < 2 ^ (prefixWord ++ tailWord_5304360).sum := by decide
  have hdescent : baseEnd_5304360 < baseStart_5304360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304373 : List Nat := [1, 3, 3, 1, 1, 1, 3, 5, 1, 2, 2]
def baseStart_5304373 : Nat := 118140960795 + 5304373 * 2 ^ 59
def prefixEnd_5304373 : Nat := 4983230072969 + 3 ^ 40 * 5304373 * 2
def baseEnd_5304373 : Nat := 2723692919731480349943139

theorem tailTrace_5304373 : CollatzResearch.WordTrace tailWord_5304373 prefixEnd_5304373 2723692919731480349943139 := by
  unfold tailWord_5304373
  simp only [CollatzResearch.WordTrace]
  refine ⟨193466377212170010629949773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128977584808113340419966515 193466377212170010629949773)
  ·
    refine ⟨72549891454563753986231165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193466377212170010629949773 72549891454563753986231165)
    ·
      refine ⟨27206209295461407744836687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72549891454563753986231165 27206209295461407744836687)
      ·
        refine ⟨40809313943192111617255031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27206209295461407744836687 40809313943192111617255031)
        ·
          refine ⟨61213970914788167425882547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40809313943192111617255031 61213970914788167425882547)
          ·
            refine ⟨91820956372182251138823821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61213970914788167425882547 91820956372182251138823821)
            ·
              refine ⟨34432858639568344177058933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91820956372182251138823821 34432858639568344177058933)
              ·
                refine ⟨3228080497459532266599275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34432858639568344177058933 3228080497459532266599275)
                ·
                  refine ⟨4842120746189298399898913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228080497459532266599275 4842120746189298399898913)
                  ·
                    refine ⟨3631590559641973799924185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4842120746189298399898913 3631590559641973799924185)
                    ·
                      refine ⟨2723692919731480349943139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3631590559641973799924185 2723692919731480349943139)
                      ·
                        rfl

theorem cell23_5304373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_5304373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304373 prefixEnd_5304373 := by exact prefixLift 5304373
  have htrace : WordTrace (prefixWord ++ tailWord_5304373) baseStart_5304373 baseEnd_5304373 := by
    simpa [prefixWord, tailWord_5304373, baseEnd_5304373] using wordTrace_append hprefix tailTrace_5304373
  have hstable : (prefixWord ++ tailWord_5304373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304373).length < 2 ^ (prefixWord ++ tailWord_5304373).sum := by decide
  have hdescent : baseEnd_5304373 < baseStart_5304373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304376 : List Nat := [2, 1, 2, 1, 6, 1, 1, 3, 1, 2, 3]
def baseStart_5304376 : Nat := 118140960795 + 5304376 * 2 ^ 59
def prefixEnd_5304376 : Nat := 4983230072969 + 3 ^ 40 * 5304376 * 2
def baseEnd_5304376 : Nat := 2723694460173443838205625

theorem tailTrace_5304376 : CollatzResearch.WordTrace tailWord_5304376 prefixEnd_5304376 2723694460173443838205625 := by
  unfold tailWord_5304376
  simp only [CollatzResearch.WordTrace]
  refine ⟨96733243315579571071154491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128977657754106094761539321 96733243315579571071154491)
  ·
    refine ⟨145099864973369356606731737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96733243315579571071154491 145099864973369356606731737)
    ·
      refine ⟨108824898730027017455048803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145099864973369356606731737 108824898730027017455048803)
      ·
        refine ⟨163237348095040526182573205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108824898730027017455048803 163237348095040526182573205)
        ·
          refine ⟨7651750691955024664808119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 163237348095040526182573205 7651750691955024664808119)
          ·
            refine ⟨11477626037932536997212179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7651750691955024664808119 11477626037932536997212179)
            ·
              refine ⟨17216439056898805495818269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11477626037932536997212179 17216439056898805495818269)
              ·
                refine ⟨6456164646337052060931851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17216439056898805495818269 6456164646337052060931851)
                ·
                  refine ⟨9684246969505578091397777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6456164646337052060931851 9684246969505578091397777)
                  ·
                    refine ⟨7263185227129183568548333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9684246969505578091397777 7263185227129183568548333)
                    ·
                      refine ⟨2723694460173443838205625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7263185227129183568548333 2723694460173443838205625)
                      ·
                        rfl

theorem cell23_5304376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_5304376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304376 prefixEnd_5304376 := by exact prefixLift 5304376
  have htrace : WordTrace (prefixWord ++ tailWord_5304376) baseStart_5304376 baseEnd_5304376 := by
    simpa [prefixWord, tailWord_5304376, baseEnd_5304376] using wordTrace_append hprefix tailTrace_5304376
  have hstable : (prefixWord ++ tailWord_5304376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304376).length < 2 ^ (prefixWord ++ tailWord_5304376).sum := by decide
  have hdescent : baseEnd_5304376 < baseStart_5304376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304390 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_5304390 : Nat := 118140960795 + 5304390 * 2 ^ 59
def prefixEnd_5304390 : Nat := 4983230072969 + 3 ^ 40 * 5304390 * 2
def baseEnd_5304390 : Nat := 2723701648902606783430561

theorem tailTrace_5304390 : CollatzResearch.WordTrace tailWord_5304390 prefixEnd_5304390 2723701648902606783430561 := by
  unfold tailWord_5304390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6045843664159638204166207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 128977998168738948355545749 6045843664159638204166207)
  ·
    refine ⟨9068765496239457306249311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6045843664159638204166207 9068765496239457306249311)
    ·
      refine ⟨13603148244359185959373967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9068765496239457306249311 13603148244359185959373967)
      ·
        refine ⟨20404722366538778939060951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13603148244359185959373967 20404722366538778939060951)
        ·
          refine ⟨30607083549808168408591427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20404722366538778939060951 30607083549808168408591427)
          ·
            refine ⟨45910625324712252612887141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30607083549808168408591427 45910625324712252612887141)
            ·
              refine ⟨8608242248383547364916339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45910625324712252612887141 8608242248383547364916339)
              ·
                refine ⟨12912363372575321047374509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8608242248383547364916339 12912363372575321047374509)
                ·
                  refine ⟨4842136264715745392765441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12912363372575321047374509 4842136264715745392765441)
                  ·
                    refine ⟨3631602198536809044574081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4842136264715745392765441 3631602198536809044574081)
                    ·
                      refine ⟨2723701648902606783430561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3631602198536809044574081 2723701648902606783430561)
                      ·
                        rfl

theorem cell23_5304390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_5304390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304390 prefixEnd_5304390 := by exact prefixLift 5304390
  have htrace : WordTrace (prefixWord ++ tailWord_5304390) baseStart_5304390 baseEnd_5304390 := by
    simpa [prefixWord, tailWord_5304390, baseEnd_5304390] using wordTrace_append hprefix tailTrace_5304390
  have hstable : (prefixWord ++ tailWord_5304390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304390).length < 2 ^ (prefixWord ++ tailWord_5304390).sum := by decide
  have hdescent : baseEnd_5304390 < baseStart_5304390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304416 : List Nat := [2, 1, 1, 3, 2, 3, 1, 4, 1, 3, 2]
def baseStart_5304416 : Nat := 118140960795 + 5304416 * 2 ^ 59
def prefixEnd_5304416 : Nat := 4983230072969 + 3 ^ 40 * 5304416 * 2
def baseEnd_5304416 : Nat := 2723714999399623681705441

theorem tailTrace_5304416 : CollatzResearch.WordTrace tailWord_5304416 prefixEnd_5304416 2723714999399623681705441 := by
  unfold tailWord_5304416
  simp only [CollatzResearch.WordTrace]
  refine ⟨96733972775507114486882551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128978630367342819315843401 96733972775507114486882551)
  ·
    refine ⟨145100959163260671730323827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96733972775507114486882551 145100959163260671730323827)
    ·
      refine ⟨217651438744891007595485741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145100959163260671730323827 217651438744891007595485741)
      ·
        refine ⟨81619289529334127848307153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217651438744891007595485741 81619289529334127848307153)
        ·
          refine ⟨61214467147000595886230365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81619289529334127848307153 61214467147000595886230365)
          ·
            refine ⟨22955425180125223457336387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61214467147000595886230365 22955425180125223457336387)
            ·
              refine ⟨34433137770187835186004581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22955425180125223457336387 34433137770187835186004581)
              ·
                refine ⟨6456213331910219097375859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34433137770187835186004581 6456213331910219097375859)
                ·
                  refine ⟨9684319997865328646063789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6456213331910219097375859 9684319997865328646063789)
                  ·
                    refine ⟨3631619999199498242273921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9684319997865328646063789 3631619999199498242273921)
                    ·
                      refine ⟨2723714999399623681705441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3631619999199498242273921 2723714999399623681705441)
                      ·
                        rfl

theorem cell23_5304416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 4, 1, 3, 2].length) (baseStart_5304416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304416 prefixEnd_5304416 := by exact prefixLift 5304416
  have htrace : WordTrace (prefixWord ++ tailWord_5304416) baseStart_5304416 baseEnd_5304416 := by
    simpa [prefixWord, tailWord_5304416, baseEnd_5304416] using wordTrace_append hprefix tailTrace_5304416
  have hstable : (prefixWord ++ tailWord_5304416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304416).length < 2 ^ (prefixWord ++ tailWord_5304416).sum := by decide
  have hdescent : baseEnd_5304416 < baseStart_5304416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304432 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 5]
def baseStart_5304432 : Nat := 118140960795 + 5304432 * 2 ^ 59
def prefixEnd_5304432 : Nat := 4983230072969 + 3 ^ 40 * 5304432 * 2
def baseEnd_5304432 : Nat := 2723723215090095619105367

theorem tailTrace_5304432 : CollatzResearch.WordTrace tailWord_5304432 prefixEnd_5304432 2723723215090095619105367 := by
  unfold tailWord_5304432
  simp only [CollatzResearch.WordTrace]
  refine ⟨96734264559478131853173775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128979019412637509137565033 96734264559478131853173775)
  ·
    refine ⟨145101396839217197779760663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96734264559478131853173775 145101396839217197779760663)
    ·
      refine ⟨217652095258825796669640995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145101396839217197779760663 217652095258825796669640995)
      ·
        refine ⟨326478142888238695004461493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217652095258825796669640995 326478142888238695004461493)
        ·
          refine ⟨30607325895772377656668265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 326478142888238695004461493 30607325895772377656668265)
          ·
            refine ⟨22955494421829283242501199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30607325895772377656668265 22955494421829283242501199)
            ·
              refine ⟨34433241632743924863751799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22955494421829283242501199 34433241632743924863751799)
              ·
                refine ⟨51649862449115887295627699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34433241632743924863751799 51649862449115887295627699)
                ·
                  refine ⟨77474793673673830943441549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51649862449115887295627699 77474793673673830943441549)
                  ·
                    refine ⟨29053047627627686603790581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77474793673673830943441549 29053047627627686603790581)
                    ·
                      refine ⟨2723723215090095619105367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29053047627627686603790581 2723723215090095619105367)
                      ·
                        rfl

theorem cell23_5304432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_5304432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304432 prefixEnd_5304432 := by exact prefixLift 5304432
  have htrace : WordTrace (prefixWord ++ tailWord_5304432) baseStart_5304432 baseEnd_5304432 := by
    simpa [prefixWord, tailWord_5304432, baseEnd_5304432] using wordTrace_append hprefix tailTrace_5304432
  have hstable : (prefixWord ++ tailWord_5304432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304432).length < 2 ^ (prefixWord ++ tailWord_5304432).sum := by decide
  have hdescent : baseEnd_5304432 < baseStart_5304432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304503 : List Nat := [1, 1, 3, 1, 4, 4, 2, 2, 5]
def baseStart_5304503 : Nat := 118140960795 + 5304503 * 2 ^ 59
def prefixEnd_5304503 : Nat := 4983230072969 + 3 ^ 40 * 5304503 * 2
def baseEnd_5304503 : Nat := 302639963579618315701949

theorem tailTrace_5304503 : CollatzResearch.WordTrace tailWord_5304503 prefixEnd_5304503 302639963579618315701949 := by
  unfold tailWord_5304503
  simp only [CollatzResearch.WordTrace]
  refine ⟨193471118701699042832182163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128980745801132695221454775 193471118701699042832182163)
  ·
    refine ⟨290206678052548564248273245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193471118701699042832182163 290206678052548564248273245)
    ·
      refine ⟨108827504269705711593102467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290206678052548564248273245 108827504269705711593102467)
      ·
        refine ⟨163241256404558567389653701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108827504269705711593102467 163241256404558567389653701)
        ·
          refine ⟨30607735575854731385560069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163241256404558567389653701 30607735575854731385560069)
          ·
            refine ⟨5738950420472762134792513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30607735575854731385560069 5738950420472762134792513)
            ·
              refine ⟨4304212815354571601094385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5738950420472762134792513 4304212815354571601094385)
              ·
                refine ⟨3228159611515928700820789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4304212815354571601094385 3228159611515928700820789)
                ·
                  refine ⟨302639963579618315701949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3228159611515928700820789 302639963579618315701949)
                  ·
                    rfl

theorem cell23_5304503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 2, 2, 5].length) (baseStart_5304503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304503 prefixEnd_5304503 := by exact prefixLift 5304503
  have htrace : WordTrace (prefixWord ++ tailWord_5304503) baseStart_5304503 baseEnd_5304503 := by
    simpa [prefixWord, tailWord_5304503, baseEnd_5304503] using wordTrace_append hprefix tailTrace_5304503
  have hstable : (prefixWord ++ tailWord_5304503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304503).length < 2 ^ (prefixWord ++ tailWord_5304503).sum := by decide
  have hdescent : baseEnd_5304503 < baseStart_5304503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304513 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_5304513 : Nat := 118140960795 + 5304513 * 2 ^ 59
def prefixEnd_5304513 : Nat := 4983230072969 + 3 ^ 40 * 5304513 * 2
def baseEnd_5304513 : Nat := 2723764807023109802192495

theorem tailTrace_5304513 : CollatzResearch.WordTrace tailWord_5304513 prefixEnd_5304513 2723764807023109802192495 := by
  unfold tailWord_5304513
  simp only [CollatzResearch.WordTrace]
  refine ⟨193471483431662814540046193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128980988954441876360030795 193471483431662814540046193)
  ·
    refine ⟨145103612573747110905034645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193471483431662814540046193 145103612573747110905034645)
    ·
      refine ⟨6801731839394395823673499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 145103612573747110905034645 6801731839394395823673499)
      ·
        refine ⟨10202597759091593735510249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6801731839394395823673499 10202597759091593735510249)
        ·
          refine ⟨7651948319318695301632687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10202597759091593735510249 7651948319318695301632687)
          ·
            refine ⟨11477922478978042952449031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7651948319318695301632687 11477922478978042952449031)
            ·
              refine ⟨17216883718467064428673547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11477922478978042952449031 17216883718467064428673547)
              ·
                refine ⟨25825325577700596643010321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17216883718467064428673547 25825325577700596643010321)
                ·
                  refine ⟨19368994183275447482257741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25825325577700596643010321 19368994183275447482257741)
                  ·
                    refine ⟨7263372818728292805846653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19368994183275447482257741 7263372818728292805846653)
                    ·
                      refine ⟨2723764807023109802192495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7263372818728292805846653 2723764807023109802192495)
                      ·
                        rfl

theorem cell23_5304513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_5304513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304513 prefixEnd_5304513 := by exact prefixLift 5304513
  have htrace : WordTrace (prefixWord ++ tailWord_5304513) baseStart_5304513 baseEnd_5304513 := by
    simpa [prefixWord, tailWord_5304513, baseEnd_5304513] using wordTrace_append hprefix tailTrace_5304513
  have hstable : (prefixWord ++ tailWord_5304513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304513).length < 2 ^ (prefixWord ++ tailWord_5304513).sum := by decide
  have hdescent : baseEnd_5304513 < baseStart_5304513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304529 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 5, 4]
def baseStart_5304529 : Nat := 118140960795 + 5304529 * 2 ^ 59
def prefixEnd_5304529 : Nat := 4983230072969 + 3 ^ 40 * 5304529 * 2
def baseEnd_5304529 : Nat := 907924340904527246530807

theorem tailTrace_5304529 : CollatzResearch.WordTrace tailWord_5304529 prefixEnd_5304529 907924340904527246530807 := by
  unfold tailWord_5304529
  simp only [CollatzResearch.WordTrace]
  refine ⟨193472066999604849272628641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128981377999736566181752427 193472066999604849272628641)
  ·
    refine ⟨145104050249703636954471481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193472066999604849272628641 145104050249703636954471481)
    ·
      refine ⟨108828037687277727715853611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145104050249703636954471481 108828037687277727715853611)
      ·
        refine ⟨163242056530916591573780417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108828037687277727715853611 163242056530916591573780417)
        ·
          refine ⟨122431542398187443680335313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163242056530916591573780417 122431542398187443680335313)
          ·
            refine ⟨91823656798640582760251485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122431542398187443680335313 91823656798640582760251485)
            ·
              refine ⟨34433871299490218535094307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91823656798640582760251485 34433871299490218535094307)
              ·
                refine ⟨51650806949235327802641461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34433871299490218535094307 51650806949235327802641461)
                ·
                  refine ⟨4842263151490811981497637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51650806949235327802641461 4842263151490811981497637)
                  ·
                    refine ⟨907924340904527246530807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4842263151490811981497637 907924340904527246530807)
                    ·
                      rfl

theorem cell23_5304529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_5304529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304529 prefixEnd_5304529 := by exact prefixLift 5304529
  have htrace : WordTrace (prefixWord ++ tailWord_5304529) baseStart_5304529 baseEnd_5304529 := by
    simpa [prefixWord, tailWord_5304529, baseEnd_5304529] using wordTrace_append hprefix tailTrace_5304529
  have hstable : (prefixWord ++ tailWord_5304529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304529).length < 2 ^ (prefixWord ++ tailWord_5304529).sum := by decide
  have hdescent : baseEnd_5304529 < baseStart_5304529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304533 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 2, 5]
def baseStart_5304533 : Nat := 118140960795 + 5304533 * 2 ^ 59
def prefixEnd_5304533 : Nat := 4983230072969 + 3 ^ 40 * 5304533 * 2
def baseEnd_5304533 : Nat := 907925025545399907980801

theorem tailTrace_5304533 : CollatzResearch.WordTrace tailWord_5304533 prefixEnd_5304533 907925025545399907980801 := by
  unfold tailWord_5304533
  simp only [CollatzResearch.WordTrace]
  refine ⟨193472212891590357955774253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128981475261060238637182835 193472212891590357955774253)
  ·
    refine ⟨72552079834346384233415345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193472212891590357955774253 72552079834346384233415345)
    ·
      refine ⟨54414059875759788175061509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72552079834346384233415345 54414059875759788175061509)
      ·
        refine ⟨10202636226704960282824033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54414059875759788175061509 10202636226704960282824033)
        ·
          refine ⟨7651977170028720212118025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10202636226704960282824033 7651977170028720212118025)
          ·
            refine ⟨5738982877521540159088519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7651977170028720212118025 5738982877521540159088519)
            ·
              refine ⟨8608474316282310238632779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5738982877521540159088519 8608474316282310238632779)
              ·
                refine ⟨12912711474423465357949169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8608474316282310238632779 12912711474423465357949169)
                ·
                  refine ⟨9684533605817599018461877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12912711474423465357949169 9684533605817599018461877)
                  ·
                    refine ⟨907925025545399907980801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9684533605817599018461877 907925025545399907980801)
                    ·
                      rfl

theorem cell23_5304533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_5304533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304533 prefixEnd_5304533 := by exact prefixLift 5304533
  have htrace : WordTrace (prefixWord ++ tailWord_5304533) baseStart_5304533 baseEnd_5304533 := by
    simpa [prefixWord, tailWord_5304533, baseEnd_5304533] using wordTrace_append hprefix tailTrace_5304533
  have hstable : (prefixWord ++ tailWord_5304533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304533).length < 2 ^ (prefixWord ++ tailWord_5304533).sum := by decide
  have hdescent : baseEnd_5304533 < baseStart_5304533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304536 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 2, 1, 4]
def baseStart_5304536 : Nat := 118140960795 + 5304536 * 2 ^ 59
def prefixEnd_5304536 : Nat := 4983230072969 + 3 ^ 40 * 5304536 * 2
def baseEnd_5304536 : Nat := 2723776617078163212204889

theorem tailTrace_5304536 : CollatzResearch.WordTrace tailWord_5304536 prefixEnd_5304536 2723776617078163212204889 := by
  unfold tailWord_5304536
  simp only [CollatzResearch.WordTrace]
  refine ⟨96736161155289744734066731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128981548207052992978755641 96736161155289744734066731)
  ·
    refine ⟨145104241732934617101100097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96736161155289744734066731 145104241732934617101100097)
    ·
      refine ⟨108828181299700962825825073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145104241732934617101100097 108828181299700962825825073)
      ·
        refine ⟨81621135974775722119368805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108828181299700962825825073 81621135974775722119368805)
        ·
          refine ⟨15303962995270447897381651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81621135974775722119368805 15303962995270447897381651)
          ·
            refine ⟨22955944492905671846072477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15303962995270447897381651 22955944492905671846072477)
            ·
              refine ⟨8608479184839626942277179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22955944492905671846072477 8608479184839626942277179)
              ·
                refine ⟨12912718777259440413415769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8608479184839626942277179 12912718777259440413415769)
                ·
                  refine ⟨9684539082944580310061827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12912718777259440413415769 9684539082944580310061827)
                  ·
                    refine ⟨14526808624416870465092741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9684539082944580310061827 14526808624416870465092741)
                    ·
                      refine ⟨2723776617078163212204889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14526808624416870465092741 2723776617078163212204889)
                      ·
                        rfl

theorem cell23_5304536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_5304536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304536 prefixEnd_5304536 := by exact prefixLift 5304536
  have htrace : WordTrace (prefixWord ++ tailWord_5304536) baseStart_5304536 baseEnd_5304536 := by
    simpa [prefixWord, tailWord_5304536, baseEnd_5304536] using wordTrace_append hprefix tailTrace_5304536
  have hstable : (prefixWord ++ tailWord_5304536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304536).length < 2 ^ (prefixWord ++ tailWord_5304536).sum := by decide
  have hdescent : baseEnd_5304536 < baseStart_5304536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304549 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 6]
def baseStart_5304549 : Nat := 118140960795 + 5304549 * 2 ^ 59
def prefixEnd_5304549 : Nat := 4983230072969 + 3 ^ 40 * 5304549 * 2
def baseEnd_5304549 : Nat := 2723783292326671661342329

theorem tailTrace_5304549 : CollatzResearch.WordTrace tailWord_5304549 prefixEnd_5304549 2723783292326671661342329 := by
  unfold tailWord_5304549
  simp only [CollatzResearch.WordTrace]
  refine ⟨193472796459532392688356701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128981864306354928458904467 193472796459532392688356701)
  ·
    refine ⟨72552298672324647258133763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193472796459532392688356701 72552298672324647258133763)
    ·
      refine ⟨108828448008486970887200645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72552298672324647258133763 108828448008486970887200645)
      ·
        refine ⟨20405334001591307041350121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108828448008486970887200645 20405334001591307041350121)
        ·
          refine ⟨15304000501193480281012591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20405334001591307041350121 15304000501193480281012591)
          ·
            refine ⟨22956000751790220421518887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15304000501193480281012591 22956000751790220421518887)
            ·
              refine ⟨34434001127685330632278331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22956000751790220421518887 34434001127685330632278331)
              ·
                refine ⟨51651001691527995948417497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34434001127685330632278331 51651001691527995948417497)
                ·
                  refine ⟨38738251268645996961313123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51651001691527995948417497 38738251268645996961313123)
                  ·
                    refine ⟨58107376902968995441969685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38738251268645996961313123 58107376902968995441969685)
                    ·
                      refine ⟨2723783292326671661342329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58107376902968995441969685 2723783292326671661342329)
                      ·
                        rfl

theorem cell23_5304549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_5304549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304549 prefixEnd_5304549 := by exact prefixLift 5304549
  have htrace : WordTrace (prefixWord ++ tailWord_5304549) baseStart_5304549 baseEnd_5304549 := by
    simpa [prefixWord, tailWord_5304549, baseEnd_5304549] using wordTrace_append hprefix tailTrace_5304549
  have hstable : (prefixWord ++ tailWord_5304549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304549).length < 2 ^ (prefixWord ++ tailWord_5304549).sum := by decide
  have hdescent : baseEnd_5304549 < baseStart_5304549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304559 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 8]
def baseStart_5304559 : Nat := 118140960795 + 5304559 * 2 ^ 59
def prefixEnd_5304559 : Nat := 4983230072969 + 3 ^ 40 * 5304559 * 2
def baseEnd_5304559 : Nat := 302643158570357402468587

theorem tailTrace_5304559 : CollatzResearch.WordTrace tailWord_5304559 prefixEnd_5304559 302643158570357402468587 := by
  unfold tailWord_5304559
  simp only [CollatzResearch.WordTrace]
  refine ⟨193473161189496164396220731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128982107459664109597480487 193473161189496164396220731)
  ·
    refine ⟨290209741784244246594331097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193473161189496164396220731 290209741784244246594331097)
    ·
      refine ⟨217657306338183184945748323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290209741784244246594331097 217657306338183184945748323)
      ·
        refine ⟨326485959507274777418622485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217657306338183184945748323 326485959507274777418622485)
        ·
          refine ⟨15304029351903505191497929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 326485959507274777418622485 15304029351903505191497929)
          ·
            refine ⟨11478022013927628893623447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15304029351903505191497929 11478022013927628893623447)
            ·
              refine ⟨17217033020891443340435171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11478022013927628893623447 17217033020891443340435171)
              ·
                refine ⟨25825549531337165010652757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17217033020891443340435171 25825549531337165010652757)
                ·
                  refine ⟨302643158570357402468587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25825549531337165010652757 302643158570357402468587)
                  ·
                    rfl

theorem cell23_5304559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 8].length) (baseStart_5304559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304559 prefixEnd_5304559 := by exact prefixLift 5304559
  have htrace : WordTrace (prefixWord ++ tailWord_5304559) baseStart_5304559 baseEnd_5304559 := by
    simpa [prefixWord, tailWord_5304559, baseEnd_5304559] using wordTrace_append hprefix tailTrace_5304559
  have hstable : (prefixWord ++ tailWord_5304559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304559).length < 2 ^ (prefixWord ++ tailWord_5304559).sum := by decide
  have hdescent : baseEnd_5304559 < baseStart_5304559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304639 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 6]
def baseStart_5304639 : Nat := 118140960795 + 5304639 * 2 ^ 59
def prefixEnd_5304639 : Nat := 4983230072969 + 3 ^ 40 * 5304639 * 2
def baseEnd_5304639 : Nat := 2723829505585576309216915

theorem tailTrace_5304639 : CollatzResearch.WordTrace tailWord_5304639 prefixEnd_5304639 2723829505585576309216915 := by
  unfold tailWord_5304639
  simp only [CollatzResearch.WordTrace]
  refine ⟨193476079029206338059132971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128984052686137558706088647 193476079029206338059132971)
  ·
    refine ⟨290214118543809507088699457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193476079029206338059132971 290214118543809507088699457)
    ·
      refine ⟨217660588907857130316524593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290214118543809507088699457 217660588907857130316524593)
      ·
        refine ⟨163245441680892847737393445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217660588907857130316524593 163245441680892847737393445)
        ·
          refine ⟨30608520315167408950761271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163245441680892847737393445 30608520315167408950761271)
          ·
            refine ⟨45912780472751113426141907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30608520315167408950761271 45912780472751113426141907)
            ·
              refine ⟨68869170709126670139212861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45912780472751113426141907 68869170709126670139212861)
              ·
                refine ⟨25825939015922501302204823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68869170709126670139212861 25825939015922501302204823)
                ·
                  refine ⟨38738908523883751953307235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25825939015922501302204823 38738908523883751953307235)
                  ·
                    refine ⟨58108362785825627929960853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38738908523883751953307235 58108362785825627929960853)
                    ·
                      refine ⟨2723829505585576309216915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58108362785825627929960853 2723829505585576309216915)
                      ·
                        rfl

theorem cell23_5304639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_5304639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304639 prefixEnd_5304639 := by exact prefixLift 5304639
  have htrace : WordTrace (prefixWord ++ tailWord_5304639) baseStart_5304639 baseEnd_5304639 := by
    simpa [prefixWord, tailWord_5304639, baseEnd_5304639] using wordTrace_append hprefix tailTrace_5304639
  have hstable : (prefixWord ++ tailWord_5304639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304639).length < 2 ^ (prefixWord ++ tailWord_5304639).sum := by decide
  have hdescent : baseEnd_5304639 < baseStart_5304639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304643 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 3, 2, 2]
def baseStart_5304643 : Nat := 118140960795 + 5304643 * 2 ^ 59
def prefixEnd_5304643 : Nat := 4983230072969 + 3 ^ 40 * 5304643 * 2
def baseEnd_5304643 : Nat := 2723831559508194293566897

theorem tailTrace_5304643 : CollatzResearch.WordTrace tailWord_5304643 prefixEnd_5304643 2723831559508194293566897 := by
  unfold tailWord_5304643
  simp only [CollatzResearch.WordTrace]
  refine ⟨193476224921191846742278583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128984149947461231161519055 193476224921191846742278583)
  ·
    refine ⟨290214337381787770113417875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193476224921191846742278583 290214337381787770113417875)
    ·
      refine ⟨435321506072681655170126813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290214337381787770113417875 435321506072681655170126813)
      ·
        refine ⟨163245564777255620688797555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435321506072681655170126813 163245564777255620688797555)
        ·
          refine ⟨244868347165883431033196333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163245564777255620688797555 244868347165883431033196333)
          ·
            refine ⟨91825630187206286637448625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244868347165883431033196333 91825630187206286637448625)
            ·
              refine ⟨68869222640404714978086469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91825630187206286637448625 68869222640404714978086469)
              ·
                refine ⟨12912979245075884058391213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68869222640404714978086469 12912979245075884058391213)
                ·
                  refine ⟨4842367216903456521896705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12912979245075884058391213 4842367216903456521896705)
                  ·
                    refine ⟨3631775412677592391422529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4842367216903456521896705 3631775412677592391422529)
                    ·
                      refine ⟨2723831559508194293566897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3631775412677592391422529 2723831559508194293566897)
                      ·
                        rfl

theorem cell23_5304643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 2, 2].length) (baseStart_5304643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304643 prefixEnd_5304643 := by exact prefixLift 5304643
  have htrace : WordTrace (prefixWord ++ tailWord_5304643) baseStart_5304643 baseEnd_5304643 := by
    simpa [prefixWord, tailWord_5304643, baseEnd_5304643] using wordTrace_append hprefix tailTrace_5304643
  have hstable : (prefixWord ++ tailWord_5304643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304643).length < 2 ^ (prefixWord ++ tailWord_5304643).sum := by decide
  have hdescent : baseEnd_5304643 < baseStart_5304643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304656 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 4]
def baseStart_5304656 : Nat := 118140960795 + 5304656 * 2 ^ 59
def prefixEnd_5304656 : Nat := 4983230072969 + 3 ^ 40 * 5304656 * 2
def baseEnd_5304656 : Nat := 2723838234756702742704337

theorem tailTrace_5304656 : CollatzResearch.WordTrace tailWord_5304656 prefixEnd_5304656 2723838234756702742704337 := by
  unfold tailWord_5304656
  simp only [CollatzResearch.WordTrace]
  refine ⟨96738349535072374981250911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128984466046763166641667881 96738349535072374981250911)
  ·
    refine ⟨145107524302608562471876367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96738349535072374981250911 145107524302608562471876367)
    ·
      refine ⟨217661286453912843707814551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145107524302608562471876367 217661286453912843707814551)
      ·
        refine ⟨326491929680869265561721827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217661286453912843707814551 326491929680869265561721827)
        ·
          refine ⟨489737894521303898342582741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326491929680869265561721827 489737894521303898342582741)
          ·
            refine ⟨11478231902843060117404283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 489737894521303898342582741 11478231902843060117404283)
            ·
              refine ⟨17217347854264590176106425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11478231902843060117404283 17217347854264590176106425)
              ·
                refine ⟨12913010890698442632079819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17217347854264590176106425 12913010890698442632079819)
                ·
                  refine ⟨19369516336047663948119729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12913010890698442632079819 19369516336047663948119729)
                  ·
                    refine ⟨14527137252035747961089797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19369516336047663948119729 14527137252035747961089797)
                    ·
                      refine ⟨2723838234756702742704337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14527137252035747961089797 2723838234756702742704337)
                      ·
                        rfl

theorem cell23_5304656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_5304656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304656 prefixEnd_5304656 := by exact prefixLift 5304656
  have htrace : WordTrace (prefixWord ++ tailWord_5304656) baseStart_5304656 baseEnd_5304656 := by
    simpa [prefixWord, tailWord_5304656, baseEnd_5304656] using wordTrace_append hprefix tailTrace_5304656
  have hstable : (prefixWord ++ tailWord_5304656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304656).length < 2 ^ (prefixWord ++ tailWord_5304656).sum := by decide
  have hdescent : baseEnd_5304656 < baseStart_5304656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304660 : List Nat := [2, 4, 1, 1, 2, 3, 3, 1, 1, 1, 4]
def baseStart_5304660 : Nat := 118140960795 + 5304660 * 2 ^ 59
def prefixEnd_5304660 : Nat := 4983230072969 + 3 ^ 40 * 5304660 * 2
def baseEnd_5304660 : Nat := 2723840288679320727054319

theorem tailTrace_5304660 : CollatzResearch.WordTrace tailWord_5304660 prefixEnd_5304660 2723840288679320727054319 := by
  unfold tailWord_5304660
  simp only [CollatzResearch.WordTrace]
  refine ⟨96738422481065129322823717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128984563308086839097098289 96738422481065129322823717)
  ·
    refine ⟨18138454215199711748029447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96738422481065129322823717 18138454215199711748029447)
    ·
      refine ⟨27207681322799567622044171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18138454215199711748029447 27207681322799567622044171)
      ·
        refine ⟨40811521984199351433066257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27207681322799567622044171 40811521984199351433066257)
        ·
          refine ⟨30608641488149513574799693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40811521984199351433066257 30608641488149513574799693)
          ·
            refine ⟨11478240558056067590549885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30608641488149513574799693 11478240558056067590549885)
            ·
              refine ⟨4304340209271025346456207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11478240558056067590549885 4304340209271025346456207)
              ·
                refine ⟨6456510313906538019684311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4304340209271025346456207 6456510313906538019684311)
                ·
                  refine ⟨9684765470859807029526467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6456510313906538019684311 9684765470859807029526467)
                  ·
                    refine ⟨14527148206289710544289701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9684765470859807029526467 14527148206289710544289701)
                    ·
                      refine ⟨2723840288679320727054319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14527148206289710544289701 2723840288679320727054319)
                      ·
                        rfl

theorem cell23_5304660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_5304660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304660 prefixEnd_5304660 := by exact prefixLift 5304660
  have htrace : WordTrace (prefixWord ++ tailWord_5304660) baseStart_5304660 baseEnd_5304660 := by
    simpa [prefixWord, tailWord_5304660, baseEnd_5304660] using wordTrace_append hprefix tailTrace_5304660
  have hstable : (prefixWord ++ tailWord_5304660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304660).length < 2 ^ (prefixWord ++ tailWord_5304660).sum := by decide
  have hdescent : baseEnd_5304660 < baseStart_5304660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304676 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 3, 3, 3]
def baseStart_5304676 : Nat := 118140960795 + 5304676 * 2 ^ 59
def prefixEnd_5304676 : Nat := 4983230072969 + 3 ^ 40 * 5304676 * 2
def baseEnd_5304676 : Nat := 2723848504369792664454245

theorem tailTrace_5304676 : CollatzResearch.WordTrace tailWord_5304676 prefixEnd_5304676 2723848504369792664454245 := by
  unfold tailWord_5304676
  simp only [CollatzResearch.WordTrace]
  refine ⟨96738714265036146689114941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128984952353381528918819921 96738714265036146689114941)
  ·
    refine ⟨36277017849388555008418103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96738714265036146689114941 36277017849388555008418103)
    ·
      refine ⟨54415526774082832512627155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36277017849388555008418103 54415526774082832512627155)
      ·
        refine ⟨81623290161124248768940733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54415526774082832512627155 81623290161124248768940733)
        ·
          refine ⟨30608733810421593288352775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81623290161124248768940733 30608733810421593288352775)
          ·
            refine ⟨45913100715632389932529163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30608733810421593288352775 45913100715632389932529163)
            ·
              refine ⟨68869651073448584898793745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45913100715632389932529163 68869651073448584898793745)
              ·
                refine ⟨51652238305086438674095309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68869651073448584898793745 51652238305086438674095309)
                ·
                  refine ⟨19369589364407414502785741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51652238305086438674095309 19369589364407414502785741)
                  ·
                    refine ⟨7263596011652780438544653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19369589364407414502785741 7263596011652780438544653)
                    ·
                      refine ⟨2723848504369792664454245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7263596011652780438544653 2723848504369792664454245)
                      ·
                        rfl

theorem cell23_5304676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_5304676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304676 prefixEnd_5304676 := by exact prefixLift 5304676
  have htrace : WordTrace (prefixWord ++ tailWord_5304676) baseStart_5304676 baseEnd_5304676 := by
    simpa [prefixWord, tailWord_5304676, baseEnd_5304676] using wordTrace_append hprefix tailTrace_5304676
  have hstable : (prefixWord ++ tailWord_5304676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304676).length < 2 ^ (prefixWord ++ tailWord_5304676).sum := by decide
  have hdescent : baseEnd_5304676 < baseStart_5304676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304677 : List Nat := [1, 3, 1, 3, 1, 4, 1, 4, 1, 2, 2]
def baseStart_5304677 : Nat := 118140960795 + 5304677 * 2 ^ 59
def prefixEnd_5304677 : Nat := 4983230072969 + 3 ^ 40 * 5304677 * 2
def baseEnd_5304677 : Nat := 2723849017850447160541741

theorem tailTrace_5304677 : CollatzResearch.WordTrace tailWord_5304677 prefixEnd_5304677 2723849017850447160541741 := by
  unfold tailWord_5304677
  simp only [CollatzResearch.WordTrace]
  refine ⟨193477465003068670549016285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128984976668712447032677523 193477465003068670549016285)
  ·
    refine ⟨72554049376150751455881107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193477465003068670549016285 72554049376150751455881107)
    ·
      refine ⟨108831074064226127183821661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72554049376150751455881107 108831074064226127183821661)
      ·
        refine ⟨40811652774084797693933123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108831074064226127183821661 40811652774084797693933123)
        ·
          refine ⟨61217479161127196540899685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40811652774084797693933123 61217479161127196540899685)
          ·
            refine ⟨11478277342711349351418691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61217479161127196540899685 11478277342711349351418691)
            ·
              refine ⟨17217416014067024027128037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11478277342711349351418691 17217416014067024027128037)
              ·
                refine ⟨3228265502637567005086507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17217416014067024027128037 3228265502637567005086507)
                ·
                  refine ⟨4842398253956350507629761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228265502637567005086507 4842398253956350507629761)
                  ·
                    refine ⟨3631798690467262880722321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4842398253956350507629761 3631798690467262880722321)
                    ·
                      refine ⟨2723849017850447160541741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3631798690467262880722321 2723849017850447160541741)
                      ·
                        rfl

theorem cell23_5304677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_5304677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304677 prefixEnd_5304677 := by exact prefixLift 5304677
  have htrace : WordTrace (prefixWord ++ tailWord_5304677) baseStart_5304677 baseEnd_5304677 := by
    simpa [prefixWord, tailWord_5304677, baseEnd_5304677] using wordTrace_append hprefix tailTrace_5304677
  have hstable : (prefixWord ++ tailWord_5304677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304677).length < 2 ^ (prefixWord ++ tailWord_5304677).sum := by decide
  have hdescent : baseEnd_5304677 < baseStart_5304677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304689 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_5304689 : Nat := 118140960795 + 5304689 * 2 ^ 59
def prefixEnd_5304689 : Nat := 4983230072969 + 3 ^ 40 * 5304689 * 2
def baseEnd_5304689 : Nat := 2723855179618301113591685

theorem tailTrace_5304689 : CollatzResearch.WordTrace tailWord_5304689 prefixEnd_5304689 2723855179618301113591685 := by
  unfold tailWord_5304689
  simp only [CollatzResearch.WordTrace]
  refine ⟨193477902679025196598453121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128985268452683464398968747 193477902679025196598453121)
  ·
    refine ⟨145108427009268897448839841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193477902679025196598453121 145108427009268897448839841)
    ·
      refine ⟨108831320256951673086629881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145108427009268897448839841 108831320256951673086629881)
      ·
        refine ⟨81623490192713754814972411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108831320256951673086629881 81623490192713754814972411)
        ·
          refine ⟨122435235289070632222458617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81623490192713754814972411 122435235289070632222458617)
          ·
            refine ⟨91826426466802974166843963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122435235289070632222458617 91826426466802974166843963)
            ·
              refine ⟨137739639700204461250265945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91826426466802974166843963 137739639700204461250265945)
              ·
                refine ⟨103304729775153345937699459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137739639700204461250265945 103304729775153345937699459)
                ·
                  refine ⟨154957094662730018906549189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103304729775153345937699459 154957094662730018906549189)
                  ·
                    refine ⟨29054455249261878544977973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 154957094662730018906549189 29054455249261878544977973)
                    ·
                      refine ⟨2723855179618301113591685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29054455249261878544977973 2723855179618301113591685)
                      ·
                        rfl

theorem cell23_5304689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_5304689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304689 prefixEnd_5304689 := by exact prefixLift 5304689
  have htrace : WordTrace (prefixWord ++ tailWord_5304689) baseStart_5304689 baseEnd_5304689 := by
    simpa [prefixWord, tailWord_5304689, baseEnd_5304689] using wordTrace_append hprefix tailTrace_5304689
  have hstable : (prefixWord ++ tailWord_5304689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304689).length < 2 ^ (prefixWord ++ tailWord_5304689).sum := by decide
  have hdescent : baseEnd_5304689 < baseStart_5304689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304693 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_5304693 : Nat := 118140960795 + 5304693 * 2 ^ 59
def prefixEnd_5304693 : Nat := 4983230072969 + 3 ^ 40 * 5304693 * 2
def baseEnd_5304693 : Nat := 2723857233540919097941667

theorem tailTrace_5304693 : CollatzResearch.WordTrace tailWord_5304693 prefixEnd_5304693 2723857233540919097941667 := by
  unfold tailWord_5304693
  simp only [CollatzResearch.WordTrace]
  refine ⟨193478048571010705281598733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128985365714007136854399155 193478048571010705281598733)
  ·
    refine ⟨72554268214129014480599525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193478048571010705281598733 72554268214129014480599525)
    ·
      refine ⟨13603925290149190215112411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72554268214129014480599525 13603925290149190215112411)
      ·
        refine ⟨20405887935223785322668617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13603925290149190215112411 20405887935223785322668617)
        ·
          refine ⟨15304415951417838992001463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20405887935223785322668617 15304415951417838992001463)
          ·
            refine ⟨22956623927126758488002195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15304415951417838992001463 22956623927126758488002195)
            ·
              refine ⟨34434935890690137732003293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22956623927126758488002195 34434935890690137732003293)
              ·
                refine ⟨12913100959008801649501235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34434935890690137732003293 12913100959008801649501235)
                ·
                  refine ⟨19369651438513202474251853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12913100959008801649501235 19369651438513202474251853)
                  ·
                    refine ⟨7263619289442450927844445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19369651438513202474251853 7263619289442450927844445)
                    ·
                      refine ⟨2723857233540919097941667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7263619289442450927844445 2723857233540919097941667)
                      ·
                        rfl

theorem cell23_5304693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_5304693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304693 prefixEnd_5304693 := by exact prefixLift 5304693
  have htrace : WordTrace (prefixWord ++ tailWord_5304693) baseStart_5304693 baseEnd_5304693 := by
    simpa [prefixWord, tailWord_5304693, baseEnd_5304693] using wordTrace_append hprefix tailTrace_5304693
  have hstable : (prefixWord ++ tailWord_5304693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304693).length < 2 ^ (prefixWord ++ tailWord_5304693).sum := by decide
  have hdescent : baseEnd_5304693 < baseStart_5304693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304694 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5304694 : Nat := 118140960795 + 5304694 * 2 ^ 59
def prefixEnd_5304694 : Nat := 4983230072969 + 3 ^ 40 * 5304694 * 2
def baseEnd_5304694 : Nat := 2723857747021573594029163

theorem tailTrace_5304694 : CollatzResearch.WordTrace tailWord_5304694 prefixEnd_5304694 2723857747021573594029163 := by
  unfold tailWord_5304694
  simp only [CollatzResearch.WordTrace]
  refine ⟨12092380315250442653274071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 128985390029338054968256757 12092380315250442653274071)
  ·
    refine ⟨18138570472875663979911107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12092380315250442653274071 18138570472875663979911107)
    ·
      refine ⟨27207855709313495969866661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18138570472875663979911107 27207855709313495969866661)
      ·
        refine ⟨5101472945496280494349999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27207855709313495969866661 5101472945496280494349999)
        ·
          refine ⟨7652209418244420741524999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5101472945496280494349999 7652209418244420741524999)
          ·
            refine ⟨11478314127366631112287499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7652209418244420741524999 11478314127366631112287499)
            ·
              refine ⟨17217471191049946668431249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11478314127366631112287499 17217471191049946668431249)
              ·
                refine ⟨12913103393287460001323437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17217471191049946668431249 12913103393287460001323437)
                ·
                  refine ⟨4842413772482797500496289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12913103393287460001323437 4842413772482797500496289)
                  ·
                    refine ⟨3631810329362098125372217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4842413772482797500496289 3631810329362098125372217)
                    ·
                      refine ⟨2723857747021573594029163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3631810329362098125372217 2723857747021573594029163)
                      ·
                        rfl

theorem cell23_5304694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5304694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304694 prefixEnd_5304694 := by exact prefixLift 5304694
  have htrace : WordTrace (prefixWord ++ tailWord_5304694) baseStart_5304694 baseEnd_5304694 := by
    simpa [prefixWord, tailWord_5304694, baseEnd_5304694] using wordTrace_append hprefix tailTrace_5304694
  have hstable : (prefixWord ++ tailWord_5304694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304694).length < 2 ^ (prefixWord ++ tailWord_5304694).sum := by decide
  have hdescent : baseEnd_5304694 < baseStart_5304694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304709 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 3, 8]
def baseStart_5304709 : Nat := 118140960795 + 5304709 * 2 ^ 59
def prefixEnd_5304709 : Nat := 4983230072969 + 3 ^ 40 * 5304709 * 2
def baseEnd_5304709 : Nat := 907955149743797011780531

theorem tailTrace_5304709 : CollatzResearch.WordTrace tailWord_5304709 prefixEnd_5304709 907955149743797011780531 := by
  unfold tailWord_5304709
  simp only [CollatzResearch.WordTrace]
  refine ⟨193478632138952740014181181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128985754759301826676120787 193478632138952740014181181)
  ·
    refine ⟨72554487052107277505317943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193478632138952740014181181 72554487052107277505317943)
    ·
      refine ⟨108831730578160916257976915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72554487052107277505317943 108831730578160916257976915)
      ·
        refine ⟨163247595867241374386965373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108831730578160916257976915 163247595867241374386965373)
        ·
          refine ⟨61217848450215515395112015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163247595867241374386965373 61217848450215515395112015)
          ·
            refine ⟨91826772675323273092668023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61217848450215515395112015 91826772675323273092668023)
            ·
              refine ⟨137740159012984909639002035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91826772675323273092668023 137740159012984909639002035)
              ·
                refine ⟨206610238519477364458503053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137740159012984909639002035 206610238519477364458503053)
                ·
                  refine ⟨77478839444804011671938645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206610238519477364458503053 77478839444804011671938645)
                  ·
                    refine ⟨907955149743797011780531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77478839444804011671938645 907955149743797011780531)
                    ·
                      rfl

theorem cell23_5304709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_5304709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304709 prefixEnd_5304709 := by exact prefixLift 5304709
  have htrace : WordTrace (prefixWord ++ tailWord_5304709) baseStart_5304709 baseEnd_5304709 := by
    simpa [prefixWord, tailWord_5304709, baseEnd_5304709] using wordTrace_append hprefix tailTrace_5304709
  have hstable : (prefixWord ++ tailWord_5304709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304709).length < 2 ^ (prefixWord ++ tailWord_5304709).sum := by decide
  have hdescent : baseEnd_5304709 < baseStart_5304709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304714 : List Nat := [3, 1, 2, 5, 1, 2, 2, 1, 1, 2, 3]
def baseStart_5304714 : Nat := 118140960795 + 5304714 * 2 ^ 59
def prefixEnd_5304714 : Nat := 4983230072969 + 3 ^ 40 * 5304714 * 2
def baseEnd_5304714 : Nat := 2723868016634663515779071

theorem tailTrace_5304714 : CollatzResearch.WordTrace tailWord_5304714 prefixEnd_5304714 2723868016634663515779071 := by
  unfold tailWord_5304714
  simp only [CollatzResearch.WordTrace]
  refine ⟨48369703625983656467028299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128985876335956417245408797 48369703625983656467028299)
  ·
    refine ⟨72554555438975484700542449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48369703625983656467028299 72554555438975484700542449)
    ·
      refine ⟨54415916579231613525406837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72554555438975484700542449 54415916579231613525406837)
      ·
        refine ⟨5101492179302963768006891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54415916579231613525406837 5101492179302963768006891)
        ·
          refine ⟨7652238268954445652010337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5101492179302963768006891 7652238268954445652010337)
          ·
            refine ⟨5739178701715834239007753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7652238268954445652010337 5739178701715834239007753)
            ·
              refine ⟨4304384026286875679255815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5739178701715834239007753 4304384026286875679255815)
              ·
                refine ⟨6456576039430313518883723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4304384026286875679255815 6456576039430313518883723)
                ·
                  refine ⟨9684864059145470278325585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6456576039430313518883723 9684864059145470278325585)
                  ·
                    refine ⟨7263648044359102708744189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9684864059145470278325585 7263648044359102708744189)
                    ·
                      refine ⟨2723868016634663515779071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7263648044359102708744189 2723868016634663515779071)
                      ·
                        rfl

theorem cell23_5304714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_5304714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304714 prefixEnd_5304714 := by exact prefixLift 5304714
  have htrace : WordTrace (prefixWord ++ tailWord_5304714) baseStart_5304714 baseEnd_5304714 := by
    simpa [prefixWord, tailWord_5304714, baseEnd_5304714] using wordTrace_append hprefix tailTrace_5304714
  have hstable : (prefixWord ++ tailWord_5304714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304714).length < 2 ^ (prefixWord ++ tailWord_5304714).sum := by decide
  have hdescent : baseEnd_5304714 < baseStart_5304714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304744 : List Nat := [2, 1, 6, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_5304744 : Nat := 118140960795 + 5304744 * 2 ^ 59
def prefixEnd_5304744 : Nat := 4983230072969 + 3 ^ 40 * 5304744 * 2
def baseEnd_5304744 : Nat := 2723883421054298398403933

theorem tailTrace_5304744 : CollatzResearch.WordTrace tailWord_5304744 prefixEnd_5304744 2723883421054298398403933 := by
  unfold tailWord_5304744
  simp only [CollatzResearch.WordTrace]
  refine ⟨96739954346912970495852643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128986605795883960661136857 96739954346912970495852643)
  ·
    refine ⟨145109931520369455743778965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96739954346912970495852643 145109931520369455743778965)
    ·
      refine ⟨6802028040017318237989639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 145109931520369455743778965 6802028040017318237989639)
      ·
        refine ⟨10203042060025977356984459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6802028040017318237989639 10203042060025977356984459)
        ·
          refine ⟨15304563090038966035476689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10203042060025977356984459 15304563090038966035476689)
          ·
            refine ⟨11478422317529224526607517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15304563090038966035476689 11478422317529224526607517)
            ·
              refine ⟨4304408369073459197477819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11478422317529224526607517 4304408369073459197477819)
              ·
                refine ⟨6456612553610188796216729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4304408369073459197477819 6456612553610188796216729)
                ·
                  refine ⟨4842459415207641597162547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6456612553610188796216729 4842459415207641597162547)
                  ·
                    refine ⟨7263689122811462395743821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4842459415207641597162547 7263689122811462395743821)
                    ·
                      refine ⟨2723883421054298398403933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7263689122811462395743821 2723883421054298398403933)
                      ·
                        rfl

theorem cell23_5304744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_5304744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304744 prefixEnd_5304744 := by exact prefixLift 5304744
  have htrace : WordTrace (prefixWord ++ tailWord_5304744) baseStart_5304744 baseEnd_5304744 := by
    simpa [prefixWord, tailWord_5304744, baseEnd_5304744] using wordTrace_append hprefix tailTrace_5304744
  have hstable : (prefixWord ++ tailWord_5304744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304744).length < 2 ^ (prefixWord ++ tailWord_5304744).sum := by decide
  have hdescent : baseEnd_5304744 < baseStart_5304744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304793 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 2, 5, 2]
def baseStart_5304793 : Nat := 118140960795 + 5304793 * 2 ^ 59
def prefixEnd_5304793 : Nat := 4983230072969 + 3 ^ 40 * 5304793 * 2
def baseEnd_5304793 : Nat := 2723908581606368706691207

theorem tailTrace_5304793 : CollatzResearch.WordTrace tailWord_5304793 prefixEnd_5304793 2723908581606368706691207 := by
  unfold tailWord_5304793
  simp only [CollatzResearch.WordTrace]
  refine ⟨193481695870648422360239033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128987797247098948240159355 193481695870648422360239033)
  ·
    refine ⟨145111271902986316770179275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193481695870648422360239033 145111271902986316770179275)
    ·
      refine ⟨217666907854479475155268913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145111271902986316770179275 217666907854479475155268913)
      ·
        refine ⟨163250180890859606366451685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217666907854479475155268913 163250180890859606366451685)
        ·
          refine ⟨30609408917036176193709691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163250180890859606366451685 30609408917036176193709691)
          ·
            refine ⟨45914113375554264290564537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30609408917036176193709691 45914113375554264290564537)
            ·
              refine ⟨34435585031665698217923403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45914113375554264290564537 34435585031665698217923403)
              ·
                refine ⟨51653377547498547326885105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34435585031665698217923403 51653377547498547326885105)
                ·
                  refine ⟨38740033160623910495163829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51653377547498547326885105 38740033160623910495163829)
                  ·
                    refine ⟨3631878108808491608921609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38740033160623910495163829 3631878108808491608921609)
                    ·
                      refine ⟨2723908581606368706691207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3631878108808491608921609 2723908581606368706691207)
                      ·
                        rfl

theorem cell23_5304793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 5, 2].length) (baseStart_5304793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304793 prefixEnd_5304793 := by exact prefixLift 5304793
  have htrace : WordTrace (prefixWord ++ tailWord_5304793) baseStart_5304793 baseEnd_5304793 := by
    simpa [prefixWord, tailWord_5304793, baseEnd_5304793] using wordTrace_append hprefix tailTrace_5304793
  have hstable : (prefixWord ++ tailWord_5304793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304793).length < 2 ^ (prefixWord ++ tailWord_5304793).sum := by decide
  have hdescent : baseEnd_5304793 < baseStart_5304793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304907 : List Nat := [1, 1, 1, 1, 3, 1, 6, 4, 1, 1, 3]
def baseStart_5304907 : Nat := 118140960795 + 5304907 * 2 ^ 59
def prefixEnd_5304907 : Nat := 4983230072969 + 3 ^ 40 * 5304907 * 2
def baseEnd_5304907 : Nat := 2723967118400981260665683

theorem tailTrace_5304907 : CollatzResearch.WordTrace tailWord_5304907 prefixEnd_5304907 2723967118400981260665683 := by
  unfold tailWord_5304907
  simp only [CollatzResearch.WordTrace]
  refine ⟨193485853792235419829888975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128990569194823613219925983 193485853792235419829888975)
  ·
    refine ⟨290228780688353129744833463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193485853792235419829888975 290228780688353129744833463)
    ·
      refine ⟨435343171032529694617250195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290228780688353129744833463 435343171032529694617250195)
      ·
        refine ⟨653014756548794541925875293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435343171032529694617250195 653014756548794541925875293)
        ·
          refine ⟨244880533705797953222203235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 653014756548794541925875293 244880533705797953222203235)
          ·
            refine ⟨367320800558696929833304853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244880533705797953222203235 367320800558696929833304853)
            ·
              refine ⟨17218162526188918585936165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 367320800558696929833304853 17218162526188918585936165)
              ·
                refine ⟨3228405473660422234863031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17218162526188918585936165 3228405473660422234863031)
                ·
                  refine ⟨4842608210490633352294547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228405473660422234863031 4842608210490633352294547)
                  ·
                    refine ⟨7263912315735950028441821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4842608210490633352294547 7263912315735950028441821)
                    ·
                      refine ⟨2723967118400981260665683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7263912315735950028441821 2723967118400981260665683)
                      ·
                        rfl

theorem cell23_5304907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 1, 1, 3].length) (baseStart_5304907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304907 prefixEnd_5304907 := by exact prefixLift 5304907
  have htrace : WordTrace (prefixWord ++ tailWord_5304907) baseStart_5304907 baseEnd_5304907 := by
    simpa [prefixWord, tailWord_5304907, baseEnd_5304907] using wordTrace_append hprefix tailTrace_5304907
  have hstable : (prefixWord ++ tailWord_5304907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304907).length < 2 ^ (prefixWord ++ tailWord_5304907).sum := by decide
  have hdescent : baseEnd_5304907 < baseStart_5304907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304941 : List Nat := [1, 5, 1, 1, 3, 3, 1, 3, 1, 1, 3]
def baseStart_5304941 : Nat := 118140960795 + 5304941 * 2 ^ 59
def prefixEnd_5304941 : Nat := 4983230072969 + 3 ^ 40 * 5304941 * 2
def baseEnd_5304941 : Nat := 2723984576743234127640527

theorem tailTrace_5304941 : CollatzResearch.WordTrace tailWord_5304941 prefixEnd_5304941 2723984576743234127640527 := by
  unfold tailWord_5304941
  simp only [CollatzResearch.WordTrace]
  refine ⟨193487093874112243636626677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128991395916074829091084451 193487093874112243636626677)
  ·
    refine ⟨18139415050698022840933751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193487093874112243636626677 18139415050698022840933751)
    ·
      refine ⟨27209122576047034261400627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18139415050698022840933751 27209122576047034261400627)
      ·
        refine ⟨40813683864070551392100941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27209122576047034261400627 40813683864070551392100941)
        ·
          refine ⟨15305131449026456772037853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40813683864070551392100941 15305131449026456772037853)
          ·
            refine ⟨5739424293384921289514195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15305131449026456772037853 5739424293384921289514195)
            ·
              refine ⟨8609136440077381934271293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5739424293384921289514195 8609136440077381934271293)
              ·
                refine ⟨3228426165029018225351735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8609136440077381934271293 3228426165029018225351735)
                ·
                  refine ⟨4842639247543527338027603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228426165029018225351735 4842639247543527338027603)
                  ·
                    refine ⟨7263958871315291007041405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4842639247543527338027603 7263958871315291007041405)
                    ·
                      refine ⟨2723984576743234127640527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7263958871315291007041405 2723984576743234127640527)
                      ·
                        rfl

theorem cell23_5304941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_5304941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304941 prefixEnd_5304941 := by exact prefixLift 5304941
  have htrace : WordTrace (prefixWord ++ tailWord_5304941) baseStart_5304941 baseEnd_5304941 := by
    simpa [prefixWord, tailWord_5304941, baseEnd_5304941] using wordTrace_append hprefix tailTrace_5304941
  have hstable : (prefixWord ++ tailWord_5304941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304941).length < 2 ^ (prefixWord ++ tailWord_5304941).sum := by decide
  have hdescent : baseEnd_5304941 < baseStart_5304941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304943 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 4]
def baseStart_5304943 : Nat := 118140960795 + 5304943 * 2 ^ 59
def prefixEnd_5304943 : Nat := 4983230072969 + 3 ^ 40 * 5304943 * 2
def baseEnd_5304943 : Nat := 2723985603704543119815517

theorem tailTrace_5304943 : CollatzResearch.WordTrace tailWord_5304943 prefixEnd_5304943 2723985603704543119815517 := by
  unfold tailWord_5304943
  simp only [CollatzResearch.WordTrace]
  refine ⟨193487166820104997978199483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128991444546736665318799655 193487166820104997978199483)
  ·
    refine ⟨290230750230157496967299225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193487166820104997978199483 290230750230157496967299225)
    ·
      refine ⟨217673062672618122725474419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290230750230157496967299225 217673062672618122725474419)
      ·
        refine ⟨326509594008927184088211629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217673062672618122725474419 326509594008927184088211629)
        ·
          refine ⟨122441097753347694033079361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326509594008927184088211629 122441097753347694033079361)
          ·
            refine ⟨91830823315010770524809521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122441097753347694033079361 91830823315010770524809521)
            ·
              refine ⟨68873117486258077893607141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91830823315010770524809521 68873117486258077893607141)
              ·
                refine ⟨12913709528673389605051339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68873117486258077893607141 12913709528673389605051339)
                ·
                  refine ⟨19370564293010084407577009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12913709528673389605051339 19370564293010084407577009)
                  ·
                    refine ⟨14527923219757563305682757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19370564293010084407577009 14527923219757563305682757)
                    ·
                      refine ⟨2723985603704543119815517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14527923219757563305682757 2723985603704543119815517)
                      ·
                        rfl

theorem cell23_5304943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_5304943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304943 prefixEnd_5304943 := by exact prefixLift 5304943
  have htrace : WordTrace (prefixWord ++ tailWord_5304943) baseStart_5304943 baseEnd_5304943 := by
    simpa [prefixWord, tailWord_5304943, baseEnd_5304943] using wordTrace_append hprefix tailTrace_5304943
  have hstable : (prefixWord ++ tailWord_5304943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304943).length < 2 ^ (prefixWord ++ tailWord_5304943).sum := by decide
  have hdescent : baseEnd_5304943 < baseStart_5304943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304953 : List Nat := [1, 2, 1, 3, 3, 4, 9]
def baseStart_5304953 : Nat := 118140960795 + 5304953 * 2 ^ 59
def prefixEnd_5304953 : Nat := 4983230072969 + 3 ^ 40 * 5304953 * 2
def baseEnd_5304953 : Nat := 33629515290260346675191

theorem tailTrace_5304953 : CollatzResearch.WordTrace tailWord_5304953 prefixEnd_5304953 33629515290260346675191 := by
  unfold tailWord_5304953
  simp only [CollatzResearch.WordTrace]
  refine ⟨193487531550068769686063513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128991687700045846457375675 193487531550068769686063513)
  ·
    refine ⟨145115648662551577264547635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193487531550068769686063513 145115648662551577264547635)
    ·
      refine ⟨217673472993827365896821453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145115648662551577264547635 217673472993827365896821453)
      ·
        refine ⟨81627552372685262211308045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217673472993827365896821453 81627552372685262211308045)
        ·
          refine ⟨30610332139756973329240517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81627552372685262211308045 30610332139756973329240517)
          ·
            refine ⟨5739437276204432499232597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30610332139756973329240517 5739437276204432499232597)
            ·
              refine ⟨33629515290260346675191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5739437276204432499232597 33629515290260346675191)
              ·
                rfl

theorem cell23_5304953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 9].length) (baseStart_5304953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304953 prefixEnd_5304953 := by exact prefixLift 5304953
  have htrace : WordTrace (prefixWord ++ tailWord_5304953) baseStart_5304953 baseEnd_5304953 := by
    simpa [prefixWord, tailWord_5304953, baseEnd_5304953] using wordTrace_append hprefix tailTrace_5304953
  have hstable : (prefixWord ++ tailWord_5304953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304953).length < 2 ^ (prefixWord ++ tailWord_5304953).sum := by decide
  have hdescent : baseEnd_5304953 < baseStart_5304953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304964 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 3, 2, 2]
def baseStart_5304964 : Nat := 118140960795 + 5304964 * 2 ^ 59
def prefixEnd_5304964 : Nat := 4983230072969 + 3 ^ 40 * 5304964 * 2
def baseEnd_5304964 : Nat := 2723996386798287537652921

theorem tailTrace_5304964 : CollatzResearch.WordTrace tailWord_5304964 prefixEnd_5304964 2723996386798287537652921 := by
  unfold tailWord_5304964
  simp only [CollatzResearch.WordTrace]
  refine ⟨96743966376514459282356973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128991955168685945709809297 96743966376514459282356973)
  ·
    refine ⟨36278987391192922230883865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96743966376514459282356973 36278987391192922230883865)
    ·
      refine ⟨27209240543394691673162899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36278987391192922230883865 27209240543394691673162899)
      ·
        refine ⟨40813860815092037509744349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27209240543394691673162899 40813860815092037509744349)
        ·
          refine ⟨15305197805659514066154131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40813860815092037509744349 15305197805659514066154131)
          ·
            refine ⟨22957796708489271099231197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15305197805659514066154131 22957796708489271099231197)
            ·
              refine ⟨8609173765683476662211699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22957796708489271099231197 8609173765683476662211699)
              ·
                refine ⟨12913760648525214993317549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8609173765683476662211699 12913760648525214993317549)
                ·
                  refine ⟨4842660243196955622494081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12913760648525214993317549 4842660243196955622494081)
                  ·
                    refine ⟨3631995182397716716870561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4842660243196955622494081 3631995182397716716870561)
                    ·
                      refine ⟨2723996386798287537652921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3631995182397716716870561 2723996386798287537652921)
                      ·
                        rfl

theorem cell23_5304964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_5304964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304964 prefixEnd_5304964 := by exact prefixLift 5304964
  have htrace : WordTrace (prefixWord ++ tailWord_5304964) baseStart_5304964 baseEnd_5304964 := by
    simpa [prefixWord, tailWord_5304964, baseEnd_5304964] using wordTrace_append hprefix tailTrace_5304964
  have hstable : (prefixWord ++ tailWord_5304964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304964).length < 2 ^ (prefixWord ++ tailWord_5304964).sum := by decide
  have hdescent : baseEnd_5304964 < baseStart_5304964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5304970 : List Nat := [3, 1, 2, 3, 3, 1, 2, 8]
def baseStart_5304970 : Nat := 118140960795 + 5304970 * 2 ^ 59
def prefixEnd_5304970 : Nat := 4983230072969 + 3 ^ 40 * 5304970 * 2
def baseEnd_5304970 : Nat := 100888869173415352376959

theorem tailTrace_5304970 : CollatzResearch.WordTrace tailWord_5304970 prefixEnd_5304970 100888869173415352376959 := by
  unfold tailWord_5304970
  simp only [CollatzResearch.WordTrace]
  refine ⟨48372037897751795397358091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 128992101060671454392954909 48372037897751795397358091)
  ·
    refine ⟨72558056846627693096037137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48372037897751795397358091 72558056846627693096037137)
    ·
      refine ⟨54418542634970769822027853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72558056846627693096037137 54418542634970769822027853)
      ·
        refine ⟨20406953488114038683260445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54418542634970769822027853 20406953488114038683260445)
        ·
          refine ⟨7652607558042764506222667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20406953488114038683260445 7652607558042764506222667)
          ·
            refine ⟨11478911337064146759334001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7652607558042764506222667 11478911337064146759334001)
            ·
              refine ⟨8609183502798110069500501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11478911337064146759334001 8609183502798110069500501)
              ·
                refine ⟨100888869173415352376959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8609183502798110069500501 100888869173415352376959)
                ·
                  rfl

theorem cell23_5304970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 8].length) (baseStart_5304970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5304970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5304970 prefixEnd_5304970 := by exact prefixLift 5304970
  have htrace : WordTrace (prefixWord ++ tailWord_5304970) baseStart_5304970 baseEnd_5304970 := by
    simpa [prefixWord, tailWord_5304970, baseEnd_5304970] using wordTrace_append hprefix tailTrace_5304970
  have hstable : (prefixWord ++ tailWord_5304970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5304970).length < 2 ^ (prefixWord ++ tailWord_5304970).sum := by decide
  have hdescent : baseEnd_5304970 < baseStart_5304970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5304970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305015 : List Nat := [1, 1, 3, 1, 7, 1, 2, 2, 1, 2, 2]
def baseStart_5305015 : Nat := 118140960795 + 5305015 * 2 ^ 59
def prefixEnd_5305015 : Nat := 4983230072969 + 3 ^ 40 * 5305015 * 2
def baseEnd_5305015 : Nat := 2724022574311666838115187

theorem tailTrace_5305015 : CollatzResearch.WordTrace tailWord_5305015 prefixEnd_5305015 2724022574311666838115187 := by
  unfold tailWord_5305015
  simp only [CollatzResearch.WordTrace]
  refine ⟨193489792875844154274820499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128993195250562769516546999 193489792875844154274820499)
  ·
    refine ⟨290234689313766231412230749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193489792875844154274820499 290234689313766231412230749)
    ·
      refine ⟨108838008492662336779586531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290234689313766231412230749 108838008492662336779586531)
      ·
        refine ⟨163257012738993505169379797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108838008492662336779586531 163257012738993505169379797)
        ·
          refine ⟨3826336236070160277407339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 163257012738993505169379797 3826336236070160277407339)
          ·
            refine ⟨5739504354105240416111009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826336236070160277407339 5739504354105240416111009)
            ·
              refine ⟨4304628265578930312083257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5739504354105240416111009 4304628265578930312083257)
              ·
                refine ⟨3228471199184197734062443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4304628265578930312083257 3228471199184197734062443)
                ·
                  refine ⟨4842706798776296601093665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228471199184197734062443 4842706798776296601093665)
                  ·
                    refine ⟨3632030099082222450820249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4842706798776296601093665 3632030099082222450820249)
                    ·
                      refine ⟨2724022574311666838115187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3632030099082222450820249 2724022574311666838115187)
                      ·
                        rfl

theorem cell23_5305015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 1, 2, 2].length) (baseStart_5305015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305015 prefixEnd_5305015 := by exact prefixLift 5305015
  have htrace : WordTrace (prefixWord ++ tailWord_5305015) baseStart_5305015 baseEnd_5305015 := by
    simpa [prefixWord, tailWord_5305015, baseEnd_5305015] using wordTrace_append hprefix tailTrace_5305015
  have hstable : (prefixWord ++ tailWord_5305015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305015).length < 2 ^ (prefixWord ++ tailWord_5305015).sum := by decide
  have hdescent : baseEnd_5305015 < baseStart_5305015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305071 : List Nat := [1, 1, 2, 1, 5, 4, 1, 2, 2, 2, 2]
def baseStart_5305071 : Nat := 118140960795 + 5305071 * 2 ^ 59
def prefixEnd_5305071 : Nat := 4983230072969 + 3 ^ 40 * 5305071 * 2
def baseEnd_5305071 : Nat := 2724051329228318619014929

theorem tailTrace_5305071 : CollatzResearch.WordTrace tailWord_5305071 prefixEnd_5305071 2724051329228318619014929 := by
  unfold tailWord_5305071
  simp only [CollatzResearch.WordTrace]
  refine ⟨193491835363641275838859067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128994556909094183892572711 193491835363641275838859067)
  ·
    refine ⟨290237753045461913758288601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193491835363641275838859067 290237753045461913758288601)
    ·
      refine ⟨217678314784096435318716451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290237753045461913758288601 217678314784096435318716451)
      ·
        refine ⟨326517472176144652978074677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217678314784096435318716451 326517472176144652978074677)
        ·
          refine ⟨30611013016513561216694501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 326517472176144652978074677 30611013016513561216694501)
          ·
            refine ⟨5739564940596292728130219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30611013016513561216694501 5739564940596292728130219)
            ·
              refine ⟨8609347410894439092195329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5739564940596292728130219 8609347410894439092195329)
              ·
                refine ⟨6457010558170829319146497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8609347410894439092195329 6457010558170829319146497)
                ·
                  refine ⟨4842757918628121989359873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6457010558170829319146497 4842757918628121989359873)
                  ·
                    refine ⟨3632068438971091492019905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4842757918628121989359873 3632068438971091492019905)
                    ·
                      refine ⟨2724051329228318619014929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3632068438971091492019905 2724051329228318619014929)
                      ·
                        rfl

theorem cell23_5305071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 2, 2].length) (baseStart_5305071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305071 prefixEnd_5305071 := by exact prefixLift 5305071
  have htrace : WordTrace (prefixWord ++ tailWord_5305071) baseStart_5305071 baseEnd_5305071 := by
    simpa [prefixWord, tailWord_5305071, baseEnd_5305071] using wordTrace_append hprefix tailTrace_5305071
  have hstable : (prefixWord ++ tailWord_5305071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305071).length < 2 ^ (prefixWord ++ tailWord_5305071).sum := by decide
  have hdescent : baseEnd_5305071 < baseStart_5305071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305083 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 5]
def baseStart_5305083 : Nat := 118140960795 + 5305083 * 2 ^ 59
def prefixEnd_5305083 : Nat := 4983230072969 + 3 ^ 40 * 5305083 * 2
def baseEnd_5305083 : Nat := 2724057490996172572064873

theorem tailTrace_5305083 : CollatzResearch.WordTrace tailWord_5305083 prefixEnd_5305083 2724057490996172572064873 := by
  unfold tailWord_5305083
  simp only [CollatzResearch.WordTrace]
  refine ⟨193492273039597801888295903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128994848693065201258863935 193492273039597801888295903)
  ·
    refine ⟨290238409559396702832443855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193492273039597801888295903 290238409559396702832443855)
    ·
      refine ⟨435357614339095054248665783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290238409559396702832443855 435357614339095054248665783)
      ·
        refine ⟨653036421508642581372998675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435357614339095054248665783 653036421508642581372998675)
        ·
          refine ⟨979554632262963872059498013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653036421508642581372998675 979554632262963872059498013)
          ·
            refine ⟨367332987098611452022311755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 979554632262963872059498013 367332987098611452022311755)
            ·
              refine ⟨550999480647917178033467633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367332987098611452022311755 550999480647917178033467633)
              ·
                refine ⟨413249610485937883525100725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550999480647917178033467633 413249610485937883525100725)
                ·
                  refine ⟨38742150983056676580478193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 413249610485937883525100725 38742150983056676580478193)
                  ·
                    refine ⟨29056613237292507435358645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38742150983056676580478193 29056613237292507435358645)
                    ·
                      refine ⟨2724057490996172572064873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29056613237292507435358645 2724057490996172572064873)
                      ·
                        rfl

theorem cell23_5305083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 5].length) (baseStart_5305083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305083 prefixEnd_5305083 := by exact prefixLift 5305083
  have htrace : WordTrace (prefixWord ++ tailWord_5305083) baseStart_5305083 baseEnd_5305083 := by
    simpa [prefixWord, tailWord_5305083, baseEnd_5305083] using wordTrace_append hprefix tailTrace_5305083
  have hstable : (prefixWord ++ tailWord_5305083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305083).length < 2 ^ (prefixWord ++ tailWord_5305083).sum := by decide
  have hdescent : baseEnd_5305083 < baseStart_5305083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305103 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 2, 8]
def baseStart_5305103 : Nat := 118140960795 + 5305103 * 2 ^ 59
def prefixEnd_5305103 : Nat := 4983230072969 + 3 ^ 40 * 5305103 * 2
def baseEnd_5305103 : Nat := 908022586869754164604927

theorem tailTrace_5305103 : CollatzResearch.WordTrace tailWord_5305103 prefixEnd_5305103 908022586869754164604927 := by
  unfold tailWord_5305103
  simp only [CollatzResearch.WordTrace]
  refine ⟨193493002499525345304023963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128995334999683563536015975 193493002499525345304023963)
  ·
    refine ⟨290239503749288017956035945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193493002499525345304023963 290239503749288017956035945)
    ·
      refine ⟨217679627811966013467026959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290239503749288017956035945 217679627811966013467026959)
      ·
        refine ⟨326519441717949020200540439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217679627811966013467026959 326519441717949020200540439)
        ·
          refine ⟨489779162576923530300810659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326519441717949020200540439 489779162576923530300810659)
          ·
            refine ⟨734668743865385295451215989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489779162576923530300810659 734668743865385295451215989)
            ·
              refine ⟨68875194737379871448551499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 734668743865385295451215989 68875194737379871448551499)
              ·
                refine ⟨103312792106069807172827249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68875194737379871448551499 103312792106069807172827249)
                ·
                  refine ⟨77484594079552355379620437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103312792106069807172827249 77484594079552355379620437)
                  ·
                    refine ⟨908022586869754164604927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 77484594079552355379620437 908022586869754164604927)
                    ·
                      rfl

theorem cell23_5305103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 8].length) (baseStart_5305103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305103 prefixEnd_5305103 := by exact prefixLift 5305103
  have htrace : WordTrace (prefixWord ++ tailWord_5305103) baseStart_5305103 baseEnd_5305103 := by
    simpa [prefixWord, tailWord_5305103, baseEnd_5305103] using wordTrace_append hprefix tailTrace_5305103
  have hstable : (prefixWord ++ tailWord_5305103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305103).length < 2 ^ (prefixWord ++ tailWord_5305103).sum := by decide
  have hdescent : baseEnd_5305103 < baseStart_5305103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305111 : List Nat := [1, 1, 3, 4, 4, 1, 1, 3, 5]
def baseStart_5305111 : Nat := 118140960795 + 5305111 * 2 ^ 59
def prefixEnd_5305111 : Nat := 4983230072969 + 3 ^ 40 * 5305111 * 2
def baseEnd_5305111 : Nat := 302674652050499829168305

theorem tailTrace_5305111 : CollatzResearch.WordTrace tailWord_5305111 prefixEnd_5305111 302674652050499829168305 := by
  unfold tailWord_5305111
  simp only [CollatzResearch.WordTrace]
  refine ⟨193493294283496362670315187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128995529522330908446876791 193493294283496362670315187)
  ·
    refine ⟨290239941425244544005472781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193493294283496362670315187 290239941425244544005472781)
    ·
      refine ⟨108839978034466704002052293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290239941425244544005472781 108839978034466704002052293)
      ·
        refine ⟨20407495881462507000384805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108839978034466704002052293 20407495881462507000384805)
        ·
          refine ⟨3826405477774220062572151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20407495881462507000384805 3826405477774220062572151)
          ·
            refine ⟨5739608216661330093858227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826405477774220062572151 5739608216661330093858227)
            ·
              refine ⟨8609412324991995140787341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5739608216661330093858227 8609412324991995140787341)
              ·
                refine ⟨3228529621871998177795253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8609412324991995140787341 3228529621871998177795253)
                ·
                  refine ⟨302674652050499829168305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3228529621871998177795253 302674652050499829168305)
                  ·
                    rfl

theorem cell23_5305111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 5].length) (baseStart_5305111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305111 prefixEnd_5305111 := by exact prefixLift 5305111
  have htrace : WordTrace (prefixWord ++ tailWord_5305111) baseStart_5305111 baseEnd_5305111 := by
    simpa [prefixWord, tailWord_5305111, baseEnd_5305111] using wordTrace_append hprefix tailTrace_5305111
  have hstable : (prefixWord ++ tailWord_5305111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305111).length < 2 ^ (prefixWord ++ tailWord_5305111).sum := by decide
  have hdescent : baseEnd_5305111 < baseStart_5305111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305164 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 2, 2, 3]
def baseStart_5305164 : Nat := 118140960795 + 5305164 * 2 ^ 59
def prefixEnd_5305164 : Nat := 4983230072969 + 3 ^ 40 * 5305164 * 2
def baseEnd_5305164 : Nat := 2724099082929186755152001

theorem tailTrace_5305164 : CollatzResearch.WordTrace tailWord_5305164 prefixEnd_5305164 2724099082929186755152001 := by
  unfold tailWord_5305164
  simp only [CollatzResearch.WordTrace]
  refine ⟨96747613676152176360997273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128996818234869568481329697 96747613676152176360997273)
  ·
    refine ⟨72560710257114132270747955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96747613676152176360997273 72560710257114132270747955)
    ·
      refine ⟨108841065385671198406121933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72560710257114132270747955 108841065385671198406121933)
      ·
        refine ⟨40815399519626699402295725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108841065385671198406121933 40815399519626699402295725)
        ·
          refine ⟨15305774819860012275860897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40815399519626699402295725 15305774819860012275860897)
          ·
            refine ⟨11479331114895009206895673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15305774819860012275860897 11479331114895009206895673)
            ·
              refine ⟨8609498336171256905171755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11479331114895009206895673 8609498336171256905171755)
              ·
                refine ⟨12914247504256885357757633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8609498336171256905171755 12914247504256885357757633)
                ·
                  refine ⟨9685685628192664018318225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12914247504256885357757633 9685685628192664018318225)
                  ·
                    refine ⟨7264264221144498013738669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9685685628192664018318225 7264264221144498013738669)
                    ·
                      refine ⟨2724099082929186755152001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7264264221144498013738669 2724099082929186755152001)
                      ·
                        rfl

theorem cell23_5305164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_5305164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305164 prefixEnd_5305164 := by exact prefixLift 5305164
  have htrace : WordTrace (prefixWord ++ tailWord_5305164) baseStart_5305164 baseEnd_5305164 := by
    simpa [prefixWord, tailWord_5305164, baseEnd_5305164] using wordTrace_append hprefix tailTrace_5305164
  have hstable : (prefixWord ++ tailWord_5305164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305164).length < 2 ^ (prefixWord ++ tailWord_5305164).sum := by decide
  have hdescent : baseEnd_5305164 < baseStart_5305164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305188 : List Nat := [2, 3, 1, 1, 4, 3, 2, 2, 1, 4]
def baseStart_5305188 : Nat := 118140960795 + 5305188 * 2 ^ 59
def prefixEnd_5305188 : Nat := 4983230072969 + 3 ^ 40 * 5305188 * 2
def baseEnd_5305188 : Nat := 908037135488298220417297

theorem tailTrace_5305188 : CollatzResearch.WordTrace tailWord_5305188 prefixEnd_5305188 908037135488298220417297 := by
  unfold tailWord_5305188
  simp only [CollatzResearch.WordTrace]
  refine ⟨96748051352108702410434109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128997401802811603213912145 96748051352108702410434109)
  ·
    refine ⟨36280519257040763403912791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96748051352108702410434109 36280519257040763403912791)
    ·
      refine ⟨54420778885561145105869187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36280519257040763403912791 54420778885561145105869187)
      ·
        refine ⟨81631168328341717658803781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54420778885561145105869187 81631168328341717658803781)
        ·
          refine ⟨15305844061564072061025709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81631168328341717658803781 15305844061564072061025709)
          ·
            refine ⟨5739691523086527022884641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15305844061564072061025709 5739691523086527022884641)
            ·
              refine ⟨4304768642314895267163481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5739691523086527022884641 4304768642314895267163481)
              ·
                refine ⟨3228576481736171450372611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4304768642314895267163481 3228576481736171450372611)
                ·
                  refine ⟨4842864722604257175558917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228576481736171450372611 4842864722604257175558917)
                  ·
                    refine ⟨908037135488298220417297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4842864722604257175558917 908037135488298220417297)
                    ·
                      rfl

theorem cell23_5305188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_5305188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305188 prefixEnd_5305188 := by exact prefixLift 5305188
  have htrace : WordTrace (prefixWord ++ tailWord_5305188) baseStart_5305188 baseEnd_5305188 := by
    simpa [prefixWord, tailWord_5305188, baseEnd_5305188] using wordTrace_append hprefix tailTrace_5305188
  have hstable : (prefixWord ++ tailWord_5305188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305188).length < 2 ^ (prefixWord ++ tailWord_5305188).sum := by decide
  have hdescent : baseEnd_5305188 < baseStart_5305188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305221 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 2, 3, 2]
def baseStart_5305221 : Nat := 118140960795 + 5305221 * 2 ^ 59
def prefixEnd_5305221 : Nat := 4983230072969 + 3 ^ 40 * 5305221 * 2
def baseEnd_5305221 : Nat := 2724128351326493032139239

theorem tailTrace_5305221 : CollatzResearch.WordTrace tailWord_5305221 prefixEnd_5305221 2724128351326493032139239 := by
  unfold tailWord_5305221
  simp only [CollatzResearch.WordTrace]
  refine ⟨193497306313097851456819517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128998204208731900971213011 193497306313097851456819517)
  ·
    refine ⟨72561489867411694296307319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193497306313097851456819517 72561489867411694296307319)
    ·
      refine ⟨108842234801117541444460979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72561489867411694296307319 108842234801117541444460979)
      ·
        refine ⟨163263352201676312166691469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108842234801117541444460979 163263352201676312166691469)
        ·
          refine ⟨61223757075628617062509301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163263352201676312166691469 61223757075628617062509301)
          ·
            refine ⟨5739727225840182849610247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61223757075628617062509301 5739727225840182849610247)
            ·
              refine ⟨8609590838760274274415371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5739727225840182849610247 8609590838760274274415371)
              ·
                refine ⟨12914386258140411411623057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8609590838760274274415371 12914386258140411411623057)
                ·
                  refine ⟨9685789693605308558717293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12914386258140411411623057 9685789693605308558717293)
                  ·
                    refine ⟨3632171135101990709518985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9685789693605308558717293 3632171135101990709518985)
                    ·
                      refine ⟨2724128351326493032139239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3632171135101990709518985 2724128351326493032139239)
                      ·
                        rfl

theorem cell23_5305221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 3, 2].length) (baseStart_5305221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305221 prefixEnd_5305221 := by exact prefixLift 5305221
  have htrace : WordTrace (prefixWord ++ tailWord_5305221) baseStart_5305221 baseEnd_5305221 := by
    simpa [prefixWord, tailWord_5305221, baseEnd_5305221] using wordTrace_append hprefix tailTrace_5305221
  have hstable : (prefixWord ++ tailWord_5305221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305221).length < 2 ^ (prefixWord ++ tailWord_5305221).sum := by decide
  have hdescent : baseEnd_5305221 < baseStart_5305221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305260 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_5305260 : Nat := 118140960795 + 5305260 * 2 ^ 59
def prefixEnd_5305260 : Nat := 4983230072969 + 3 ^ 40 * 5305260 * 2
def baseEnd_5305260 : Nat := 2724148377072018379551559

theorem tailTrace_5305260 : CollatzResearch.WordTrace tailWord_5305260 prefixEnd_5305260 2724148377072018379551559 := by
  unfold tailWord_5305260
  simp only [CollatzResearch.WordTrace]
  refine ⟨96749364379978280558744617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128999152506637707411659489 96749364379978280558744617)
  ·
    refine ⟨72562023284983710419058463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96749364379978280558744617 72562023284983710419058463)
    ·
      refine ⟨108843034927475565628587695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72562023284983710419058463 108843034927475565628587695)
      ·
        refine ⟨163264552391213348442881543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108843034927475565628587695 163264552391213348442881543)
        ·
          refine ⟨244896828586820022664322315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163264552391213348442881543 244896828586820022664322315)
          ·
            refine ⟨367345242880230033996483473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244896828586820022664322315 367345242880230033996483473)
            ·
              refine ⟨275508932160172525497362605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367345242880230033996483473 275508932160172525497362605)
              ·
                refine ⟨103315849560064697061510977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275508932160172525497362605 103315849560064697061510977)
                ·
                  refine ⟨77486887170048522796133233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103315849560064697061510977 77486887170048522796133233)
                  ·
                    refine ⟨58115165377536392097099925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77486887170048522796133233 58115165377536392097099925)
                    ·
                      refine ⟨2724148377072018379551559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58115165377536392097099925 2724148377072018379551559)
                      ·
                        rfl

theorem cell23_5305260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_5305260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305260 prefixEnd_5305260 := by exact prefixLift 5305260
  have htrace : WordTrace (prefixWord ++ tailWord_5305260) baseStart_5305260 baseEnd_5305260 := by
    simpa [prefixWord, tailWord_5305260, baseEnd_5305260] using wordTrace_append hprefix tailTrace_5305260
  have hstable : (prefixWord ++ tailWord_5305260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305260).length < 2 ^ (prefixWord ++ tailWord_5305260).sum := by decide
  have hdescent : baseEnd_5305260 < baseStart_5305260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305267 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 3]
def baseStart_5305267 : Nat := 118140960795 + 5305267 * 2 ^ 59
def prefixEnd_5305267 : Nat := 4983230072969 + 3 ^ 40 * 5305267 * 2
def baseEnd_5305267 : Nat := 2724151971436599852164027

theorem tailTrace_5305267 : CollatzResearch.WordTrace tailWord_5305267 prefixEnd_5305267 2724151971436599852164027 := by
  unfold tailWord_5305267
  simp only [CollatzResearch.WordTrace]
  refine ⟨193498984070931201312994055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 128999322713954134208662703 193498984070931201312994055)
  ·
    refine ⟨290248476106396801969491083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193498984070931201312994055 290248476106396801969491083)
    ·
      refine ⟨435372714159595202954236625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290248476106396801969491083 435372714159595202954236625)
      ·
        refine ⟨326529535619696402215677469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435372714159595202954236625 326529535619696402215677469)
        ·
          refine ⟨122448575857386150830879051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326529535619696402215677469 122448575857386150830879051)
          ·
            refine ⟨183672863786079226246318577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122448575857386150830879051 183672863786079226246318577)
            ·
              refine ⟨137754647839559419684738933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183672863786079226246318577 137754647839559419684738933)
              ·
                refine ⟨12914498234958695595444275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137754647839559419684738933 12914498234958695595444275)
                ·
                  refine ⟨19371747352438043393166413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12914498234958695595444275 19371747352438043393166413)
                  ·
                    refine ⟨7264405257164266272437405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19371747352438043393166413 7264405257164266272437405)
                    ·
                      refine ⟨2724151971436599852164027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7264405257164266272437405 2724151971436599852164027)
                      ·
                        rfl

theorem cell23_5305267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3, 3].length) (baseStart_5305267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305267 prefixEnd_5305267 := by exact prefixLift 5305267
  have htrace : WordTrace (prefixWord ++ tailWord_5305267) baseStart_5305267 baseEnd_5305267 := by
    simpa [prefixWord, tailWord_5305267, baseEnd_5305267] using wordTrace_append hprefix tailTrace_5305267
  have hstable : (prefixWord ++ tailWord_5305267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305267).length < 2 ^ (prefixWord ++ tailWord_5305267).sum := by decide
  have hdescent : baseEnd_5305267 < baseStart_5305267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305268 : List Nat := [2, 5, 2, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_5305268 : Nat := 118140960795 + 5305268 * 2 ^ 59
def prefixEnd_5305268 : Nat := 4983230072969 + 3 ^ 40 * 5305268 * 2
def baseEnd_5305268 : Nat := 2724152484917254348251523

theorem tailTrace_5305268 : CollatzResearch.WordTrace tailWord_5305268 prefixEnd_5305268 2724152484917254348251523 := by
  unfold tailWord_5305268
  simp only [CollatzResearch.WordTrace]
  refine ⟨96749510271963789241890229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 128999347029285052322520305 96749510271963789241890229)
  ·
    refine ⟨9070266587996605241427209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96749510271963789241890229 9070266587996605241427209)
    ·
      refine ⟨6802699940997453931070407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9070266587996605241427209 6802699940997453931070407)
      ·
        refine ⟨10204049911496180896605611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6802699940997453931070407 10204049911496180896605611)
        ·
          refine ⟨15306074867244271344908417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10204049911496180896605611 15306074867244271344908417)
          ·
            refine ⟨11479556150433203508681313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15306074867244271344908417 11479556150433203508681313)
            ·
              refine ⟨8609667112824902631510985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11479556150433203508681313 8609667112824902631510985)
              ·
                refine ⟨6457250334618676973633239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8609667112824902631510985 6457250334618676973633239)
                ·
                  refine ⟨9685875501928015460449859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6457250334618676973633239 9685875501928015460449859)
                  ·
                    refine ⟨14528813252892023190674789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9685875501928015460449859 14528813252892023190674789)
                    ·
                      refine ⟨2724152484917254348251523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14528813252892023190674789 2724152484917254348251523)
                      ·
                        rfl

theorem cell23_5305268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_5305268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305268 prefixEnd_5305268 := by exact prefixLift 5305268
  have htrace : WordTrace (prefixWord ++ tailWord_5305268) baseStart_5305268 baseEnd_5305268 := by
    simpa [prefixWord, tailWord_5305268, baseEnd_5305268] using wordTrace_append hprefix tailTrace_5305268
  have hstable : (prefixWord ++ tailWord_5305268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305268).length < 2 ^ (prefixWord ++ tailWord_5305268).sum := by decide
  have hdescent : baseEnd_5305268 < baseStart_5305268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305327 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 5]
def baseStart_5305327 : Nat := 118140960795 + 5305327 * 2 ^ 59
def prefixEnd_5305327 : Nat := 4983230072969 + 3 ^ 40 * 5305327 * 2
def baseEnd_5305327 : Nat := 2724182780275869617413751

theorem tailTrace_5305327 : CollatzResearch.WordTrace tailWord_5305327 prefixEnd_5305327 2724182780275869617413751 := by
  unfold tailWord_5305327
  simp only [CollatzResearch.WordTrace]
  refine ⟨193501172450713831560178235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129000781633809221040118823 193501172450713831560178235)
  ·
    refine ⟨290251758676070747340267353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193501172450713831560178235 290251758676070747340267353)
    ·
      refine ⟨217688819007053060505200515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290251758676070747340267353 217688819007053060505200515)
      ·
        refine ⟨326533228510579590757800773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217688819007053060505200515 326533228510579590757800773)
        ·
          refine ⟨61224980345733673267087645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 326533228510579590757800773 61224980345733673267087645)
          ·
            refine ⟨22959367629650127475157867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61224980345733673267087645 22959367629650127475157867)
            ·
              refine ⟨34439051444475191212736801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22959367629650127475157867 34439051444475191212736801)
              ·
                refine ⟨25829288583356393409552601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34439051444475191212736801 25829288583356393409552601)
                ·
                  refine ⟨19371966437517295057164451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25829288583356393409552601 19371966437517295057164451)
                  ·
                    refine ⟨29057949656275942585746677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19371966437517295057164451 29057949656275942585746677)
                    ·
                      refine ⟨2724182780275869617413751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29057949656275942585746677 2724182780275869617413751)
                      ·
                        rfl

theorem cell23_5305327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_5305327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305327 prefixEnd_5305327 := by exact prefixLift 5305327
  have htrace : WordTrace (prefixWord ++ tailWord_5305327) baseStart_5305327 baseEnd_5305327 := by
    simpa [prefixWord, tailWord_5305327, baseEnd_5305327] using wordTrace_append hprefix tailTrace_5305327
  have hstable : (prefixWord ++ tailWord_5305327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305327).length < 2 ^ (prefixWord ++ tailWord_5305327).sum := by decide
  have hdescent : baseEnd_5305327 < baseStart_5305327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305358 : List Nat := [4, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2]
def baseStart_5305358 : Nat := 118140960795 + 5305358 * 2 ^ 59
def prefixEnd_5305358 : Nat := 4983230072969 + 3 ^ 40 * 5305358 * 2
def baseEnd_5305358 : Nat := 2724198698176158996126109

theorem tailTrace_5305358 : CollatzResearch.WordTrace tailWord_5305358 prefixEnd_5305358 2724198698176158996126109 := by
  unfold tailWord_5305358
  simp only [CollatzResearch.WordTrace]
  refine ⟨24187787889200190481819591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129001535409067682569704485 24187787889200190481819591)
  ·
    refine ⟨36281681833800285722729387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24187787889200190481819591 36281681833800285722729387)
    ·
      refine ⟨54422522750700428584094081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36281681833800285722729387 54422522750700428584094081)
      ·
        refine ⟨40816892063025321438070561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54422522750700428584094081 40816892063025321438070561)
        ·
          refine ⟨30612669047268991078552921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40816892063025321438070561 30612669047268991078552921)
          ·
            refine ⟨22959501785451743308914691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30612669047268991078552921 22959501785451743308914691)
            ·
              refine ⟨34439252678177614963372037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22959501785451743308914691 34439252678177614963372037)
              ·
                refine ⟨6457359877158302805632257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34439252678177614963372037 6457359877158302805632257)
                ·
                  refine ⟨4843019907868727104224193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6457359877158302805632257 4843019907868727104224193)
                  ·
                    refine ⟨3632264930901545328168145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4843019907868727104224193 3632264930901545328168145)
                    ·
                      refine ⟨2724198698176158996126109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3632264930901545328168145 2724198698176158996126109)
                      ·
                        rfl

theorem cell23_5305358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_5305358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305358 prefixEnd_5305358 := by exact prefixLift 5305358
  have htrace : WordTrace (prefixWord ++ tailWord_5305358) baseStart_5305358 baseEnd_5305358 := by
    simpa [prefixWord, tailWord_5305358, baseEnd_5305358] using wordTrace_append hprefix tailTrace_5305358
  have hstable : (prefixWord ++ tailWord_5305358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305358).length < 2 ^ (prefixWord ++ tailWord_5305358).sum := by decide
  have hdescent : baseEnd_5305358 < baseStart_5305358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305398 : List Nat := [5, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_5305398 : Nat := 118140960795 + 5305398 * 2 ^ 59
def prefixEnd_5305398 : Nat := 4983230072969 + 3 ^ 40 * 5305398 * 2
def baseEnd_5305398 : Nat := 302691026378037648847325

theorem tailTrace_5305398 : CollatzResearch.WordTrace tailWord_5305398 prefixEnd_5305398 302691026378037648847325 := by
  unfold tailWord_5305398
  simp only [CollatzResearch.WordTrace]
  refine ⟨12093985127091038167875803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129002508022304407124008565 12093985127091038167875803)
  ·
    refine ⟨18140977690636557251813705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12093985127091038167875803 18140977690636557251813705)
    ·
      refine ⟨13605733267977417938860279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18140977690636557251813705 13605733267977417938860279)
      ·
        refine ⟨20408599901966126908290419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13605733267977417938860279 20408599901966126908290419)
        ·
          refine ⟨30612899852949190362435629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20408599901966126908290419 30612899852949190362435629)
          ·
            refine ⟨11479837444855946385913361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30612899852949190362435629 11479837444855946385913361)
            ·
              refine ⟨8609878083641959789435021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11479837444855946385913361 8609878083641959789435021)
              ·
                refine ⟨3228704281365734921038133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8609878083641959789435021 3228704281365734921038133)
                ·
                  refine ⟨302691026378037648847325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3228704281365734921038133 302691026378037648847325)
                  ·
                    rfl

theorem cell23_5305398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_5305398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305398 prefixEnd_5305398 := by exact prefixLift 5305398
  have htrace : WordTrace (prefixWord ++ tailWord_5305398) baseStart_5305398 baseEnd_5305398 := by
    simpa [prefixWord, tailWord_5305398, baseEnd_5305398] using wordTrace_append hprefix tailTrace_5305398
  have hstable : (prefixWord ++ tailWord_5305398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305398).length < 2 ^ (prefixWord ++ tailWord_5305398).sum := by decide
  have hdescent : baseEnd_5305398 < baseStart_5305398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305427 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 4]
def baseStart_5305427 : Nat := 118140960795 + 5305427 * 2 ^ 59
def prefixEnd_5305427 : Nat := 4983230072969 + 3 ^ 40 * 5305427 * 2
def baseEnd_5305427 : Nat := 2724234128341319226163291

theorem tailTrace_5305427 : CollatzResearch.WordTrace tailWord_5305427 prefixEnd_5305427 2724234128341319226163291 := by
  unfold tailWord_5305427
  simp only [CollatzResearch.WordTrace]
  refine ⟨193504819750351548638818535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129003213166901032425879023 193504819750351548638818535)
  ·
    refine ⟨290257229625527322958227803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193504819750351548638818535 290257229625527322958227803)
    ·
      refine ⟨435385844438290984437341705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290257229625527322958227803 435385844438290984437341705)
      ·
        refine ⟨326539383328718238328006279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435385844438290984437341705 326539383328718238328006279)
        ·
          refine ⟨489809074993077357492009419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326539383328718238328006279 489809074993077357492009419)
          ·
            refine ⟨734713612489616036238014129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489809074993077357492009419 734713612489616036238014129)
            ·
              refine ⟨551035209367212027178510597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734713612489616036238014129 551035209367212027178510597)
              ·
                refine ⟨103319101756352255095970737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 551035209367212027178510597 103319101756352255095970737)
                ·
                  refine ⟨77489326317264191321978053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103319101756352255095970737 77489326317264191321978053)
                  ·
                    refine ⟨14529248684487035872870885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77489326317264191321978053 14529248684487035872870885)
                    ·
                      refine ⟨2724234128341319226163291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14529248684487035872870885 2724234128341319226163291)
                      ·
                        rfl

theorem cell23_5305427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_5305427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305427 prefixEnd_5305427 := by exact prefixLift 5305427
  have htrace : WordTrace (prefixWord ++ tailWord_5305427) baseStart_5305427 baseEnd_5305427 := by
    simpa [prefixWord, tailWord_5305427, baseEnd_5305427] using wordTrace_append hprefix tailTrace_5305427
  have hstable : (prefixWord ++ tailWord_5305427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305427).length < 2 ^ (prefixWord ++ tailWord_5305427).sum := by decide
  have hdescent : baseEnd_5305427 < baseStart_5305427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305434 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3]
def baseStart_5305434 : Nat := 118140960795 + 5305434 * 2 ^ 59
def prefixEnd_5305434 : Nat := 4983230072969 + 3 ^ 40 * 5305434 * 2
def baseEnd_5305434 : Nat := 2724237722705900698775759

theorem tailTrace_5305434 : CollatzResearch.WordTrace tailWord_5305434 prefixEnd_5305434 2724237722705900698775759 := by
  unfold tailWord_5305434
  simp only [CollatzResearch.WordTrace]
  refine ⟨48376268765331547208580839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129003383374217459222882237 48376268765331547208580839)
  ·
    refine ⟨72564403147997320812871259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48376268765331547208580839 72564403147997320812871259)
    ·
      refine ⟨108846604721995981219306889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72564403147997320812871259 108846604721995981219306889)
      ·
        refine ⟨81634953541496985914480167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108846604721995981219306889 81634953541496985914480167)
        ·
          refine ⟨122452430312245478871720251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81634953541496985914480167 122452430312245478871720251)
          ·
            refine ⟨183678645468368218307580377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122452430312245478871720251 183678645468368218307580377)
            ·
              refine ⟨137758984101276163730685283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183678645468368218307580377 137758984101276163730685283)
              ·
                refine ⟨206638476151914245596027925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137758984101276163730685283 206638476151914245596027925)
                ·
                  refine ⟨9686178569620980262313809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 206638476151914245596027925 9686178569620980262313809)
                  ·
                    refine ⟨7264633927215735196735357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9686178569620980262313809 7264633927215735196735357)
                    ·
                      refine ⟨2724237722705900698775759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7264633927215735196735357 2724237722705900698775759)
                      ·
                        rfl

theorem cell23_5305434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_5305434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305434 prefixEnd_5305434 := by exact prefixLift 5305434
  have htrace : WordTrace (prefixWord ++ tailWord_5305434) baseStart_5305434 baseEnd_5305434 := by
    simpa [prefixWord, tailWord_5305434, baseEnd_5305434] using wordTrace_append hprefix tailTrace_5305434
  have hstable : (prefixWord ++ tailWord_5305434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305434).length < 2 ^ (prefixWord ++ tailWord_5305434).sum := by decide
  have hdescent : baseEnd_5305434 < baseStart_5305434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305454 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 8]
def baseStart_5305454 : Nat := 118140960795 + 5305454 * 2 ^ 59
def prefixEnd_5305454 : Nat := 4983230072969 + 3 ^ 40 * 5305454 * 2
def baseEnd_5305454 : Nat := 302694221368776735613963

theorem tailTrace_5305454 : CollatzResearch.WordTrace tailWord_5305454 prefixEnd_5305454 302694221368776735613963 := by
  unfold tailWord_5305454
  simp only [CollatzResearch.WordTrace]
  refine ⟨24188225565156716531256427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129003869680835821500034277 24188225565156716531256427)
  ·
    refine ⟨36282338347735074796884641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24188225565156716531256427 36282338347735074796884641)
    ·
      refine ⟨27211753760801306097663481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36282338347735074796884641 27211753760801306097663481)
      ·
        refine ⟨20408815320600979573247611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27211753760801306097663481 20408815320600979573247611)
        ·
          refine ⟨30613222980901469359871417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20408815320600979573247611 30613222980901469359871417)
          ·
            refine ⟨22959917235676102019903563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30613222980901469359871417 22959917235676102019903563)
            ·
              refine ⟨34439875853514153029855345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22959917235676102019903563 34439875853514153029855345)
              ·
                refine ⟨25829906890135614772391509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34439875853514153029855345 25829906890135614772391509)
                ·
                  refine ⟨302694221368776735613963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25829906890135614772391509 302694221368776735613963)
                  ·
                    rfl

theorem cell23_5305454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_5305454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305454 prefixEnd_5305454 := by exact prefixLift 5305454
  have htrace : WordTrace (prefixWord ++ tailWord_5305454) baseStart_5305454 baseEnd_5305454 := by
    simpa [prefixWord, tailWord_5305454, baseEnd_5305454] using wordTrace_append hprefix tailTrace_5305454
  have hstable : (prefixWord ++ tailWord_5305454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305454).length < 2 ^ (prefixWord ++ tailWord_5305454).sum := by decide
  have hdescent : baseEnd_5305454 < baseStart_5305454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305457 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_5305457 : Nat := 118140960795 + 5305457 * 2 ^ 59
def prefixEnd_5305457 : Nat := 4983230072969 + 3 ^ 40 * 5305457 * 2
def baseEnd_5305457 : Nat := 2724249532760954108788153

theorem tailTrace_5305457 : CollatzResearch.WordTrace tailWord_5305457 prefixEnd_5305457 2724249532760954108788153 := by
  unfold tailWord_5305457
  simp only [CollatzResearch.WordTrace]
  refine ⟨193505913940242863762410625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129003942626828575841607083 193505913940242863762410625)
  ·
    refine ⟨145129435455182147821807969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193505913940242863762410625 145129435455182147821807969)
    ·
      refine ⟨108847076591386610866355977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145129435455182147821807969 108847076591386610866355977)
      ·
        refine ⟨81635307443539958149766983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108847076591386610866355977 81635307443539958149766983)
        ·
          refine ⟨122452961165309937224650475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81635307443539958149766983 122452961165309937224650475)
          ·
            refine ⟨183679441747964905836975713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122452961165309937224650475 183679441747964905836975713)
            ·
              refine ⟨137759581310973679377731785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183679441747964905836975713 137759581310973679377731785)
              ·
                refine ⟨103319685983230259533298839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137759581310973679377731785 103319685983230259533298839)
                ·
                  refine ⟨154979528974845389299948259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103319685983230259533298839 154979528974845389299948259)
                  ·
                    refine ⟨232469293462268083949922389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 154979528974845389299948259 232469293462268083949922389)
                    ·
                      refine ⟨2724249532760954108788153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 232469293462268083949922389 2724249532760954108788153)
                      ·
                        rfl

theorem cell23_5305457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_5305457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305457 prefixEnd_5305457 := by exact prefixLift 5305457
  have htrace : WordTrace (prefixWord ++ tailWord_5305457) baseStart_5305457 baseEnd_5305457 := by
    simpa [prefixWord, tailWord_5305457, baseEnd_5305457] using wordTrace_append hprefix tailTrace_5305457
  have hstable : (prefixWord ++ tailWord_5305457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305457).length < 2 ^ (prefixWord ++ tailWord_5305457).sum := by decide
  have hdescent : baseEnd_5305457 < baseStart_5305457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305508 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 2, 3, 2]
def baseStart_5305508 : Nat := 118140960795 + 5305508 * 2 ^ 59
def prefixEnd_5305508 : Nat := 4983230072969 + 3 ^ 40 * 5305508 * 2
def baseEnd_5305508 : Nat := 2724275720274333409250419

theorem tailTrace_5305508 : CollatzResearch.WordTrace tailWord_5305508 prefixEnd_5305508 2724275720274333409250419 := by
  unfold tailWord_5305508
  simp only [CollatzResearch.WordTrace]
  refine ⟨96753887031529049736258589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129005182708705399648344785 96753887031529049736258589)
  ·
    refine ⟨36282707636823393651096971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96753887031529049736258589 36282707636823393651096971)
    ·
      refine ⟨54424061455235090476645457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36282707636823393651096971 54424061455235090476645457)
      ·
        refine ⟨40818046091426317857484093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54424061455235090476645457 40818046091426317857484093)
        ·
          refine ⟨15306767284284869196556535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40818046091426317857484093 15306767284284869196556535)
          ·
            refine ⟨22960150926427303794834803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15306767284284869196556535 22960150926427303794834803)
            ·
              refine ⟨34440226389640955692252205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22960150926427303794834803 34440226389640955692252205)
              ·
                refine ⟨12915084896115358384594577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34440226389640955692252205 12915084896115358384594577)
                ·
                  refine ⟨9686313672086518788445933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12915084896115358384594577 9686313672086518788445933)
                  ·
                    refine ⟨3632367627032444545667225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9686313672086518788445933 3632367627032444545667225)
                    ·
                      refine ⟨2724275720274333409250419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3632367627032444545667225 2724275720274333409250419)
                      ·
                        rfl

theorem cell23_5305508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_5305508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305508 prefixEnd_5305508 := by exact prefixLift 5305508
  have htrace : WordTrace (prefixWord ++ tailWord_5305508) baseStart_5305508 baseEnd_5305508 := by
    simpa [prefixWord, tailWord_5305508, baseEnd_5305508] using wordTrace_append hprefix tailTrace_5305508
  have hstable : (prefixWord ++ tailWord_5305508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305508).length < 2 ^ (prefixWord ++ tailWord_5305508).sum := by decide
  have hdescent : baseEnd_5305508 < baseStart_5305508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305526 : List Nat := [5, 1, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_5305526 : Nat := 118140960795 + 5305526 * 2 ^ 59
def prefixEnd_5305526 : Nat := 4983230072969 + 3 ^ 40 * 5305526 * 2
def baseEnd_5305526 : Nat := 908094987642038112941779

theorem tailTrace_5305526 : CollatzResearch.WordTrace tailWord_5305526 prefixEnd_5305526 908094987642038112941779 := by
  unfold tailWord_5305526
  simp only [CollatzResearch.WordTrace]
  refine ⟨12094276911062055534167027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129005620384661925697781621 12094276911062055534167027)
  ·
    refine ⟨18141415366593083301250541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12094276911062055534167027 18141415366593083301250541)
    ·
      refine ⟨6803030762472406237968953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18141415366593083301250541 6803030762472406237968953)
      ·
        refine ⟨5102273071854304678476715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6803030762472406237968953 5102273071854304678476715)
        ·
          refine ⟨7653409607781457017715073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5102273071854304678476715 7653409607781457017715073)
          ·
            refine ⟨5740057205836092763286305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7653409607781457017715073 5740057205836092763286305)
            ·
              refine ⟨4305042904377069572464729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5740057205836092763286305 4305042904377069572464729)
              ·
                refine ⟨3228782178282802179348547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4305042904377069572464729 3228782178282802179348547)
                ·
                  refine ⟨4843173267424203269022821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228782178282802179348547 4843173267424203269022821)
                  ·
                    refine ⟨908094987642038112941779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4843173267424203269022821 908094987642038112941779)
                    ·
                      rfl

theorem cell23_5305526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_5305526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305526 prefixEnd_5305526 := by exact prefixLift 5305526
  have htrace : WordTrace (prefixWord ++ tailWord_5305526) baseStart_5305526 baseEnd_5305526 := by
    simpa [prefixWord, tailWord_5305526, baseEnd_5305526] using wordTrace_append hprefix tailTrace_5305526
  have hstable : (prefixWord ++ tailWord_5305526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305526).length < 2 ^ (prefixWord ++ tailWord_5305526).sum := by decide
  have hdescent : baseEnd_5305526 < baseStart_5305526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305532 : List Nat := [2, 2, 2, 3, 2, 1, 4, 2, 1, 1, 3]
def baseStart_5305532 : Nat := 118140960795 + 5305532 * 2 ^ 59
def prefixEnd_5305532 : Nat := 4983230072969 + 3 ^ 40 * 5305532 * 2
def baseEnd_5305532 : Nat := 2724288043810041315350309

theorem tailTrace_5305532 : CollatzResearch.WordTrace tailWord_5305532 prefixEnd_5305532 2724288043810041315350309 := by
  unfold tailWord_5305532
  simp only [CollatzResearch.WordTrace]
  refine ⟨96754324707485575785695425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129005766276647434380927233 96754324707485575785695425)
  ·
    refine ⟨72565743530614181839271569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96754324707485575785695425 72565743530614181839271569)
    ·
      refine ⟨54424307647960636379453677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72565743530614181839271569 54424307647960636379453677)
      ·
        refine ⟨20409115367985238642295129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54424307647960636379453677 20409115367985238642295129)
        ·
          refine ⟨15306836525988928981721347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20409115367985238642295129 15306836525988928981721347)
          ·
            refine ⟨22960254788983393472582021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15306836525988928981721347 22960254788983393472582021)
            ·
              refine ⟨4305047772934386276109129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22960254788983393472582021 4305047772934386276109129)
              ·
                refine ⟨3228785829700789707081847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4305047772934386276109129 3228785829700789707081847)
                ·
                  refine ⟨4843178744551184560622771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228785829700789707081847 4843178744551184560622771)
                  ·
                    refine ⟨7264768116826776840934157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4843178744551184560622771 7264768116826776840934157)
                    ·
                      refine ⟨2724288043810041315350309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7264768116826776840934157 2724288043810041315350309)
                      ·
                        rfl

theorem cell23_5305532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_5305532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305532 prefixEnd_5305532 := by exact prefixLift 5305532
  have htrace : WordTrace (prefixWord ++ tailWord_5305532) baseStart_5305532 baseEnd_5305532 := by
    simpa [prefixWord, tailWord_5305532, baseEnd_5305532] using wordTrace_append hprefix tailTrace_5305532
  have hstable : (prefixWord ++ tailWord_5305532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305532).length < 2 ^ (prefixWord ++ tailWord_5305532).sum := by decide
  have hdescent : baseEnd_5305532 < baseStart_5305532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305544 : List Nat := [2, 1, 3, 1, 2, 1, 5, 8]
def baseStart_5305544 : Nat := 118140960795 + 5305544 * 2 ^ 59
def prefixEnd_5305544 : Nat := 4983230072969 + 3 ^ 40 * 5305544 * 2
def baseEnd_5305544 : Nat := 100899785391773898829639

theorem tailTrace_5305544 : CollatzResearch.WordTrace tailWord_5305544 prefixEnd_5305544 100899785391773898829639 := by
  unfold tailWord_5305544
  simp only [CollatzResearch.WordTrace]
  refine ⟨96754543545463838810413843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129006058060618451747218457 96754543545463838810413843)
  ·
    refine ⟨145131815318195758215620765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96754543545463838810413843 145131815318195758215620765)
    ·
      refine ⟨54424430744323409330857787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145131815318195758215620765 54424430744323409330857787)
      ·
        refine ⟨81636646116485113996286681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54424430744323409330857787 81636646116485113996286681)
        ·
          refine ⟨61227484587363835497215011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81636646116485113996286681 61227484587363835497215011)
          ·
            refine ⟨91841226881045753245822517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61227484587363835497215011 91841226881045753245822517)
            ·
              refine ⟨8610115020098039366795861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91841226881045753245822517 8610115020098039366795861)
              ·
                refine ⟨100899785391773898829639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8610115020098039366795861 100899785391773898829639)
                ·
                  rfl

theorem cell23_5305544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 8].length) (baseStart_5305544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305544 prefixEnd_5305544 := by exact prefixLift 5305544
  have htrace : WordTrace (prefixWord ++ tailWord_5305544) baseStart_5305544 baseEnd_5305544 := by
    simpa [prefixWord, tailWord_5305544, baseEnd_5305544] using wordTrace_append hprefix tailTrace_5305544
  have hstable : (prefixWord ++ tailWord_5305544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305544).length < 2 ^ (prefixWord ++ tailWord_5305544).sum := by decide
  have hdescent : baseEnd_5305544 < baseStart_5305544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305575 : List Nat := [1, 1, 5, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_5305575 : Nat := 118140960795 + 5305575 * 2 ^ 59
def prefixEnd_5305575 : Nat := 4983230072969 + 3 ^ 40 * 5305575 * 2
def baseEnd_5305575 : Nat := 2724310123478184647112611

theorem tailTrace_5305575 : CollatzResearch.WordTrace tailWord_5305575 prefixEnd_5305575 2724310123478184647112611 := by
  unfold tailWord_5305575
  simp only [CollatzResearch.WordTrace]
  refine ⟨193510217753815369915206179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129006811835876913276804119 193510217753815369915206179)
  ·
    refine ⟨290265326630723054872809269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193510217753815369915206179 290265326630723054872809269)
    ·
      refine ⟨27212374371630286394325869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 290265326630723054872809269 27212374371630286394325869)
      ·
        refine ⟨10204640389361357397872201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27212374371630286394325869 10204640389361357397872201)
        ·
          refine ⟨7653480292021018048404151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10204640389361357397872201 7653480292021018048404151)
          ·
            refine ⟨11480220438031527072606227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7653480292021018048404151 11480220438031527072606227)
            ·
              refine ⟨17220330657047290608909341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11480220438031527072606227 17220330657047290608909341)
              ·
                refine ⟨6457623996392733978341003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17220330657047290608909341 6457623996392733978341003)
                ·
                  refine ⟨9686435994589100967511505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6457623996392733978341003 9686435994589100967511505)
                  ·
                    refine ⟨7264826995941825725633629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9686435994589100967511505 7264826995941825725633629)
                    ·
                      refine ⟨2724310123478184647112611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7264826995941825725633629 2724310123478184647112611)
                      ·
                        rfl

theorem cell23_5305575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_5305575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305575 prefixEnd_5305575 := by exact prefixLift 5305575
  have htrace : WordTrace (prefixWord ++ tailWord_5305575) baseStart_5305575 baseEnd_5305575 := by
    simpa [prefixWord, tailWord_5305575, baseEnd_5305575] using wordTrace_append hprefix tailTrace_5305575
  have hstable : (prefixWord ++ tailWord_5305575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305575).length < 2 ^ (prefixWord ++ tailWord_5305575).sum := by decide
  have hdescent : baseEnd_5305575 < baseStart_5305575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305602 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_5305602 : Nat := 118140960795 + 5305602 * 2 ^ 59
def prefixEnd_5305602 : Nat := 4983230072969 + 3 ^ 40 * 5305602 * 2
def baseEnd_5305602 : Nat := 2724323987455856041474987

theorem tailTrace_5305602 : CollatzResearch.WordTrace tailWord_5305602 prefixEnd_5305602 2724323987455856041474987 := by
  unfold tailWord_5305602
  simp only [CollatzResearch.WordTrace]
  refine ⟨48377800631179388381609765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129007468349811702350959373 48377800631179388381609765)
  ·
    refine ⟨9070837618346135321551831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48377800631179388381609765 9070837618346135321551831)
    ·
      refine ⟨13606256427519202982327747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9070837618346135321551831 13606256427519202982327747)
      ·
        refine ⟨20409384641278804473491621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13606256427519202982327747 20409384641278804473491621)
        ·
          refine ⟨3826759620239775838779679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20409384641278804473491621 3826759620239775838779679)
          ·
            refine ⟨5740139430359663758169519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826759620239775838779679 5740139430359663758169519)
            ·
              refine ⟨8610209145539495637254279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5740139430359663758169519 8610209145539495637254279)
              ·
                refine ⟨12915313718309243455881419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8610209145539495637254279 12915313718309243455881419)
                ·
                  refine ⟨19372970577463865183822129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12915313718309243455881419 19372970577463865183822129)
                  ·
                    refine ⟨14529727933097898887866597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19372970577463865183822129 14529727933097898887866597)
                    ·
                      refine ⟨2724323987455856041474987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14529727933097898887866597 2724323987455856041474987)
                      ·
                        rfl

theorem cell23_5305602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_5305602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305602 prefixEnd_5305602 := by exact prefixLift 5305602
  have htrace : WordTrace (prefixWord ++ tailWord_5305602) baseStart_5305602 baseEnd_5305602 := by
    simpa [prefixWord, tailWord_5305602, baseEnd_5305602] using wordTrace_append hprefix tailTrace_5305602
  have hstable : (prefixWord ++ tailWord_5305602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305602).length < 2 ^ (prefixWord ++ tailWord_5305602).sum := by decide
  have hdescent : baseEnd_5305602 < baseStart_5305602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305605 : List Nat := [1, 3, 1, 1, 2, 1, 7, 1, 2, 1, 3]
def baseStart_5305605 : Nat := 118140960795 + 5305605 * 2 ^ 59
def prefixEnd_5305605 : Nat := 4983230072969 + 3 ^ 40 * 5305605 * 2
def baseEnd_5305605 : Nat := 2724325527897819529737473

theorem tailTrace_5305605 : CollatzResearch.WordTrace tailWord_5305605 prefixEnd_5305605 2724325527897819529737473 := by
  unfold tailWord_5305605
  simp only [CollatzResearch.WordTrace]
  refine ⟨193511311943706685038798269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129007541295804456692532179 193511311943706685038798269)
  ·
    refine ⟨72566741978890006889549351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193511311943706685038798269 72566741978890006889549351)
    ·
      refine ⟨108850112968335010334324027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72566741978890006889549351 108850112968335010334324027)
      ·
        refine ⟨163275169452502515501486041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108850112968335010334324027 163275169452502515501486041)
        ·
          refine ⟨122456377089376886626114531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163275169452502515501486041 122456377089376886626114531)
          ·
            refine ⟨183684565634065329939171797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122456377089376886626114531 183684565634065329939171797)
            ·
              refine ⟨4305107007048406170449339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 183684565634065329939171797 4305107007048406170449339)
              ·
                refine ⟨6457660510572609255674009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4305107007048406170449339 6457660510572609255674009)
                ·
                  refine ⟨4843245382929456941755507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6457660510572609255674009 4843245382929456941755507)
                  ·
                    refine ⟨7264868074394185412633261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4843245382929456941755507 7264868074394185412633261)
                    ·
                      refine ⟨2724325527897819529737473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7264868074394185412633261 2724325527897819529737473)
                      ·
                        rfl

theorem cell23_5305605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 2, 1, 3].length) (baseStart_5305605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305605 prefixEnd_5305605 := by exact prefixLift 5305605
  have htrace : WordTrace (prefixWord ++ tailWord_5305605) baseStart_5305605 baseEnd_5305605 := by
    simpa [prefixWord, tailWord_5305605, baseEnd_5305605] using wordTrace_append hprefix tailTrace_5305605
  have hstable : (prefixWord ++ tailWord_5305605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305605).length < 2 ^ (prefixWord ++ tailWord_5305605).sum := by decide
  have hdescent : baseEnd_5305605 < baseStart_5305605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305628 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 1, 4, 2]
def baseStart_5305628 : Nat := 118140960795 + 5305628 * 2 ^ 59
def prefixEnd_5305628 : Nat := 4983230072969 + 3 ^ 40 * 5305628 * 2
def baseEnd_5305628 : Nat := 2724337337952872939749867

theorem tailTrace_5305628 : CollatzResearch.WordTrace tailWord_5305628 prefixEnd_5305628 2724337337952872939749867 := by
  unfold tailWord_5305628
  simp only [CollatzResearch.WordTrace]
  refine ⟨96756075411311679983442769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129008100548415573311257025 96756075411311679983442769)
  ·
    refine ⟨72567056558483759987582077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96756075411311679983442769 72567056558483759987582077)
    ·
      refine ⟨27212646209431409995343279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72567056558483759987582077 27212646209431409995343279)
      ·
        refine ⟨40818969314147114993014919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27212646209431409995343279 40818969314147114993014919)
        ·
          refine ⟨61228453971220672489522379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40818969314147114993014919 61228453971220672489522379)
          ·
            refine ⟨91842680956831008734283569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61228453971220672489522379 91842680956831008734283569)
            ·
              refine ⟨68882010717623256550712677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91842680956831008734283569 68882010717623256550712677)
              ·
                refine ⟨12915377009554360603258627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68882010717623256550712677 12915377009554360603258627)
                ·
                  refine ⟨19373065514331540904887941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12915377009554360603258627 19373065514331540904887941)
                  ·
                    refine ⟨3632449783937163919666489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19373065514331540904887941 3632449783937163919666489)
                    ·
                      refine ⟨2724337337952872939749867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3632449783937163919666489 2724337337952872939749867)
                      ·
                        rfl

theorem cell23_5305628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_5305628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305628 prefixEnd_5305628 := by exact prefixLift 5305628
  have htrace : WordTrace (prefixWord ++ tailWord_5305628) baseStart_5305628 baseEnd_5305628 := by
    simpa [prefixWord, tailWord_5305628, baseEnd_5305628] using wordTrace_append hprefix tailTrace_5305628
  have hstable : (prefixWord ++ tailWord_5305628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305628).length < 2 ^ (prefixWord ++ tailWord_5305628).sum := by decide
  have hdescent : baseEnd_5305628 < baseStart_5305628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305644 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_5305644 : Nat := 118140960795 + 5305644 * 2 ^ 59
def prefixEnd_5305644 : Nat := 4983230072969 + 3 ^ 40 * 5305644 * 2
def baseEnd_5305644 : Nat := 2724345553643344877149793

theorem tailTrace_5305644 : CollatzResearch.WordTrace tailWord_5305644 prefixEnd_5305644 2724345553643344877149793 := by
  unfold tailWord_5305644
  simp only [CollatzResearch.WordTrace]
  refine ⟨96756367195282697349733993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129008489593710263132978657 96756367195282697349733993)
  ·
    refine ⟨72567275396462023012300495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96756367195282697349733993 72567275396462023012300495)
    ·
      refine ⟨108850913094693034518450743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72567275396462023012300495 108850913094693034518450743)
      ·
        refine ⟨163276369642039551777676115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108850913094693034518450743 163276369642039551777676115)
        ·
          refine ⟨244914554463059327666514173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163276369642039551777676115 244914554463059327666514173)
          ·
            refine ⟨91842957923647247874942815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244914554463059327666514173 91842957923647247874942815)
            ·
              refine ⟨137764436885470871812414223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91842957923647247874942815 137764436885470871812414223)
              ·
                refine ⟨206646655328206307718621335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137764436885470871812414223 206646655328206307718621335)
                ·
                  refine ⟨309969982992309461577932003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206646655328206307718621335 309969982992309461577932003)
                  ·
                    refine ⟨464954974488464192366898005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 309969982992309461577932003 464954974488464192366898005)
                    ·
                      refine ⟨2724345553643344877149793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 464954974488464192366898005 2724345553643344877149793)
                      ·
                        rfl

theorem cell23_5305644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_5305644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305644 prefixEnd_5305644 := by exact prefixLift 5305644
  have htrace : WordTrace (prefixWord ++ tailWord_5305644) baseStart_5305644 baseEnd_5305644 := by
    simpa [prefixWord, tailWord_5305644, baseEnd_5305644] using wordTrace_append hprefix tailTrace_5305644
  have hstable : (prefixWord ++ tailWord_5305644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305644).length < 2 ^ (prefixWord ++ tailWord_5305644).sum := by decide
  have hdescent : baseEnd_5305644 < baseStart_5305644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305651 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 7]
def baseStart_5305651 : Nat := 118140960795 + 5305651 * 2 ^ 59
def prefixEnd_5305651 : Nat := 4983230072969 + 3 ^ 40 * 5305651 * 2
def baseEnd_5305651 : Nat := 302705460889769594418029

theorem tailTrace_5305651 : CollatzResearch.WordTrace tailWord_5305651 prefixEnd_5305651 302705460889769594418029 := by
  unfold tailWord_5305651
  simp only [CollatzResearch.WordTrace]
  refine ⟨193512989701540034894972807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129008659801026689929981871 193512989701540034894972807)
  ·
    refine ⟨290269484552310052342459211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193512989701540034894972807 290269484552310052342459211)
    ·
      refine ⟨435404226828465078513688817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290269484552310052342459211 435404226828465078513688817)
      ·
        refine ⟨326553170121348808885266613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435404226828465078513688817 326553170121348808885266613)
        ·
          refine ⟨30614359698876450832993745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 326553170121348808885266613 30614359698876450832993745)
          ·
            refine ⟨22960769774157338124745309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30614359698876450832993745 22960769774157338124745309)
            ·
              refine ⟨8610288665309001796779491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22960769774157338124745309 8610288665309001796779491)
              ·
                refine ⟨12915432997963502695169237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8610288665309001796779491 12915432997963502695169237)
                ·
                  refine ⟨302705460889769594418029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12915432997963502695169237 302705460889769594418029)
                  ·
                    rfl

theorem cell23_5305651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 7].length) (baseStart_5305651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305651 prefixEnd_5305651 := by exact prefixLift 5305651
  have htrace : WordTrace (prefixWord ++ tailWord_5305651) baseStart_5305651 baseEnd_5305651 := by
    simpa [prefixWord, tailWord_5305651, baseEnd_5305651] using wordTrace_append hprefix tailTrace_5305651
  have hstable : (prefixWord ++ tailWord_5305651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305651).length < 2 ^ (prefixWord ++ tailWord_5305651).sum := by decide
  have hdescent : baseEnd_5305651 < baseStart_5305651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305662 : List Nat := [4, 2, 1, 2, 1, 1, 3, 3, 2, 2, 2]
def baseStart_5305662 : Nat := 118140960795 + 5305662 * 2 ^ 59
def prefixEnd_5305662 : Nat := 4983230072969 + 3 ^ 40 * 5305662 * 2
def baseEnd_5305662 : Nat := 2724354796295125806724711

theorem tailTrace_5305662 : CollatzResearch.WordTrace tailWord_5305662 prefixEnd_5305662 2724354796295125806724711 := by
  unfold tailWord_5305662
  simp only [CollatzResearch.WordTrace]
  refine ⟨24189173863062522971702905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129008927269666789182415493 24189173863062522971702905)
  ·
    refine ⟨18141880397296892228777179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24189173863062522971702905 18141880397296892228777179)
    ·
      refine ⟨27212820595945338343165769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18141880397296892228777179 27212820595945338343165769)
      ·
        refine ⟨20409615446959003757374327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27212820595945338343165769 20409615446959003757374327)
        ·
          refine ⟨30614423170438505636061491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20409615446959003757374327 30614423170438505636061491)
          ·
            refine ⟨45921634755657758454092237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30614423170438505636061491 45921634755657758454092237)
            ·
              refine ⟨17220613033371659420284589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45921634755657758454092237 17220613033371659420284589)
              ·
                refine ⟨6457729887514372282606721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17220613033371659420284589 6457729887514372282606721)
                ·
                  refine ⟨4843297415635779211955041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6457729887514372282606721 4843297415635779211955041)
                  ·
                    refine ⟨3632473061726834408966281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4843297415635779211955041 3632473061726834408966281)
                    ·
                      refine ⟨2724354796295125806724711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3632473061726834408966281 2724354796295125806724711)
                      ·
                        rfl

theorem cell23_5305662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_5305662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305662 prefixEnd_5305662 := by exact prefixLift 5305662
  have htrace : WordTrace (prefixWord ++ tailWord_5305662) baseStart_5305662 baseEnd_5305662 := by
    simpa [prefixWord, tailWord_5305662, baseEnd_5305662] using wordTrace_append hprefix tailTrace_5305662
  have hstable : (prefixWord ++ tailWord_5305662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305662).length < 2 ^ (prefixWord ++ tailWord_5305662).sum := by decide
  have hdescent : baseEnd_5305662 < baseStart_5305662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305698 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_5305698 : Nat := 118140960795 + 5305698 * 2 ^ 59
def prefixEnd_5305698 : Nat := 4983230072969 + 3 ^ 40 * 5305698 * 2
def baseEnd_5305698 : Nat := 908124427199562555291515

theorem tailTrace_5305698 : CollatzResearch.WordTrace tailWord_5305698 prefixEnd_5305698 908124427199562555291515 := by
  unfold tailWord_5305698
  simp only [CollatzResearch.WordTrace]
  refine ⟨48378675983092440480483437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129009802621579841281289165 48378675983092440480483437)
  ·
    refine ⟨18142003493659665180181289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48378675983092440480483437 18142003493659665180181289)
    ·
      refine ⟨13606502620244748885135967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18142003493659665180181289 13606502620244748885135967)
      ·
        refine ⟨20409753930367123327703951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13606502620244748885135967 20409753930367123327703951)
        ·
          refine ⟨30614630895550684991555927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20409753930367123327703951 30614630895550684991555927)
          ·
            refine ⟨45921946343326027487333891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30614630895550684991555927 45921946343326027487333891)
            ·
              refine ⟨68882919514989041231000837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45921946343326027487333891 68882919514989041231000837)
              ·
                refine ⟨12915547409060445230812657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68882919514989041231000837 12915547409060445230812657)
                ·
                  refine ⟨9686660556795333923109493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12915547409060445230812657 9686660556795333923109493)
                  ·
                    refine ⟨908124427199562555291515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9686660556795333923109493 908124427199562555291515)
                    ·
                      rfl

theorem cell23_5305698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_5305698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305698 prefixEnd_5305698 := by exact prefixLift 5305698
  have htrace : WordTrace (prefixWord ++ tailWord_5305698) baseStart_5305698 baseEnd_5305698 := by
    simpa [prefixWord, tailWord_5305698, baseEnd_5305698] using wordTrace_append hprefix tailTrace_5305698
  have hstable : (prefixWord ++ tailWord_5305698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305698).length < 2 ^ (prefixWord ++ tailWord_5305698).sum := by decide
  have hdescent : baseEnd_5305698 < baseStart_5305698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305735 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 2, 1, 4]
def baseStart_5305735 : Nat := 118140960795 + 5305735 * 2 ^ 59
def prefixEnd_5305735 : Nat := 4983230072969 + 3 ^ 40 * 5305735 * 2
def baseEnd_5305735 : Nat := 2724392280382904021111875

theorem tailTrace_5305735 : CollatzResearch.WordTrace tailWord_5305735 prefixEnd_5305735 2724392280382904021111875 := by
  unfold tailWord_5305735
  simp only [CollatzResearch.WordTrace]
  refine ⟨193516053433235717241030659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129010702288823811494020439 193516053433235717241030659)
  ·
    refine ⟨290274080149853575861545989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193516053433235717241030659 290274080149853575861545989)
    ·
      refine ⟨54426390028097545474039873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290274080149853575861545989 54426390028097545474039873)
      ·
        refine ⟨40819792521073159105529905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54426390028097545474039873 40819792521073159105529905)
        ·
          refine ⟨30614844390804869329147429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40819792521073159105529905 30614844390804869329147429)
          ·
            refine ⟨5740283323275912999215143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30614844390804869329147429 5740283323275912999215143)
            ·
              refine ⟨8610424984913869498822715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5740283323275912999215143 8610424984913869498822715)
              ·
                refine ⟨12915637477370804248234073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8610424984913869498822715 12915637477370804248234073)
                ·
                  refine ⟨9686728108028103186175555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12915637477370804248234073 9686728108028103186175555)
                  ·
                    refine ⟨14530092162042154779263333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9686728108028103186175555 14530092162042154779263333)
                    ·
                      refine ⟨2724392280382904021111875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14530092162042154779263333 2724392280382904021111875)
                      ·
                        rfl

theorem cell23_5305735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_5305735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305735 prefixEnd_5305735 := by exact prefixLift 5305735
  have htrace : WordTrace (prefixWord ++ tailWord_5305735) baseStart_5305735 baseEnd_5305735 := by
    simpa [prefixWord, tailWord_5305735, baseEnd_5305735] using wordTrace_append hprefix tailTrace_5305735
  have hstable : (prefixWord ++ tailWord_5305735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305735).length < 2 ^ (prefixWord ++ tailWord_5305735).sum := by decide
  have hdescent : baseEnd_5305735 < baseStart_5305735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305748 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_5305748 : Nat := 118140960795 + 5305748 * 2 ^ 59
def prefixEnd_5305748 : Nat := 4983230072969 + 3 ^ 40 * 5305748 * 2
def baseEnd_5305748 : Nat := 2724398955631412470249315

theorem tailTrace_5305748 : CollatzResearch.WordTrace tailWord_5305748 prefixEnd_5305748 2724398955631412470249315 := by
  unfold tailWord_5305748
  simp only [CollatzResearch.WordTrace]
  refine ⟨96758263791094310230626949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129011018388125746974169265 96758263791094310230626949)
  ·
    refine ⟨18142174460830183168242553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96758263791094310230626949 18142174460830183168242553)
    ·
      refine ⟨13606630845622637376181915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18142174460830183168242553 13606630845622637376181915)
      ·
        refine ⟨20409946268433956064272873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13606630845622637376181915 20409946268433956064272873)
        ·
          refine ⟨15307459701325467048204655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20409946268433956064272873 15307459701325467048204655)
          ·
            refine ⟨22961189551988200572306983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15307459701325467048204655 22961189551988200572306983)
            ·
              refine ⟨34441784327982300858460475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22961189551988200572306983 34441784327982300858460475)
              ·
                refine ⟨51662676491973451287690713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34441784327982300858460475 51662676491973451287690713)
                ·
                  refine ⟨38747007368980088465768035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51662676491973451287690713 38747007368980088465768035)
                  ·
                    refine ⟨58120511053470132698652053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38747007368980088465768035 58120511053470132698652053)
                    ·
                      refine ⟨2724398955631412470249315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58120511053470132698652053 2724398955631412470249315)
                      ·
                        rfl

theorem cell23_5305748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_5305748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305748 prefixEnd_5305748 := by exact prefixLift 5305748
  have htrace : WordTrace (prefixWord ++ tailWord_5305748) baseStart_5305748 baseEnd_5305748 := by
    simpa [prefixWord, tailWord_5305748, baseEnd_5305748] using wordTrace_append hprefix tailTrace_5305748
  have hstable : (prefixWord ++ tailWord_5305748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305748).length < 2 ^ (prefixWord ++ tailWord_5305748).sum := by decide
  have hdescent : baseEnd_5305748 < baseStart_5305748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305762 : List Nat := [3, 3, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_5305762 : Nat := 118140960795 + 5305762 * 2 ^ 59
def prefixEnd_5305762 : Nat := 4983230072969 + 3 ^ 40 * 5305762 * 2
def baseEnd_5305762 : Nat := 908135381453525138491417

theorem tailTrace_5305762 : CollatzResearch.WordTrace tailWord_5305762 prefixEnd_5305762 908135381453525138491417 := by
  unfold tailWord_5305762
  simp only [CollatzResearch.WordTrace]
  refine ⟨48379259551034475213065885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129011358802758600568175693 48379259551034475213065885)
  ·
    refine ⟨18142222331637928204899707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48379259551034475213065885 18142222331637928204899707)
    ·
      refine ⟨27213333497456892307349561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18142222331637928204899707 27213333497456892307349561)
      ·
        refine ⟨20410000123092669230512171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27213333497456892307349561 20410000123092669230512171)
        ·
          refine ⟨30615000184639003845768257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20410000123092669230512171 30615000184639003845768257)
          ·
            refine ⟨22961250138479252884326193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30615000184639003845768257 22961250138479252884326193)
            ·
              refine ⟨17220937603859439663244645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22961250138479252884326193 17220937603859439663244645)
              ·
                refine ⟨3228925800723644936858371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17220937603859439663244645 3228925800723644936858371)
                ·
                  refine ⟨4843388701085467405287557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3228925800723644936858371 4843388701085467405287557)
                  ·
                    refine ⟨908135381453525138491417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4843388701085467405287557 908135381453525138491417)
                    ·
                      rfl

theorem cell23_5305762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_5305762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305762 prefixEnd_5305762 := by exact prefixLift 5305762
  have htrace : WordTrace (prefixWord ++ tailWord_5305762) baseStart_5305762 baseEnd_5305762 := by
    simpa [prefixWord, tailWord_5305762, baseEnd_5305762] using wordTrace_append hprefix tailTrace_5305762
  have hstable : (prefixWord ++ tailWord_5305762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305762).length < 2 ^ (prefixWord ++ tailWord_5305762).sum := by decide
  have hdescent : baseEnd_5305762 < baseStart_5305762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305791 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 4]
def baseStart_5305791 : Nat := 118140960795 + 5305791 * 2 ^ 59
def prefixEnd_5305791 : Nat := 4983230072969 + 3 ^ 40 * 5305791 * 2
def baseEnd_5305791 : Nat := 2724421035299555802011617

theorem tailTrace_5305791 : CollatzResearch.WordTrace tailWord_5305791 prefixEnd_5305791 2724421035299555802011617 := by
  unfold tailWord_5305791
  simp only [CollatzResearch.WordTrace]
  refine ⟨193518095921032838805069227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129012063947355225870046151 193518095921032838805069227)
  ·
    refine ⟨290277143881549258207603841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193518095921032838805069227 290277143881549258207603841)
    ·
      refine ⟨217707857911161943655702881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290277143881549258207603841 217707857911161943655702881)
      ·
        refine ⟨163280893433371457741777161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217707857911161943655702881 163280893433371457741777161)
        ·
          refine ⟨122460670075028593306332871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163280893433371457741777161 122460670075028593306332871)
          ·
            refine ⟨183691005112542889959499307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122460670075028593306332871 183691005112542889959499307)
            ·
              refine ⟨275536507668814334939248961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183691005112542889959499307 275536507668814334939248961)
              ·
                refine ⟨206652380751610751204436721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275536507668814334939248961 206652380751610751204436721)
                ·
                  refine ⟨154989285563708063403327541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 206652380751610751204436721 154989285563708063403327541)
                  ·
                    refine ⟨14530245521597630944061957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 154989285563708063403327541 14530245521597630944061957)
                    ·
                      refine ⟨2724421035299555802011617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14530245521597630944061957 2724421035299555802011617)
                      ·
                        rfl

theorem cell23_5305791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_5305791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305791 prefixEnd_5305791 := by exact prefixLift 5305791
  have htrace : WordTrace (prefixWord ++ tailWord_5305791) baseStart_5305791 baseEnd_5305791 := by
    simpa [prefixWord, tailWord_5305791, baseEnd_5305791] using wordTrace_append hprefix tailTrace_5305791
  have hstable : (prefixWord ++ tailWord_5305791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305791).length < 2 ^ (prefixWord ++ tailWord_5305791).sum := by decide
  have hdescent : baseEnd_5305791 < baseStart_5305791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305801 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 3, 6]
def baseStart_5305801 : Nat := 118140960795 + 5305801 * 2 ^ 59
def prefixEnd_5305801 : Nat := 4983230072969 + 3 ^ 40 * 5305801 * 2
def baseEnd_5305801 : Nat := 908142056702033587628857

theorem tailTrace_5305801 : CollatzResearch.WordTrace tailWord_5305801 prefixEnd_5305801 908142056702033587628857 := by
  unfold tailWord_5305801
  simp only [CollatzResearch.WordTrace]
  refine ⟨193518460650996610512933257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129012307100664407008622171 193518460650996610512933257)
  ·
    refine ⟨145138845488247457884699943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193518460650996610512933257 145138845488247457884699943)
    ·
      refine ⟨217708268232371186827049915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145138845488247457884699943 217708268232371186827049915)
      ·
        refine ⟨326562402348556780240574873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217708268232371186827049915 326562402348556780240574873)
        ·
          refine ⟨244921801761417585180431155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326562402348556780240574873 244921801761417585180431155)
          ·
            refine ⟨367382702642126377770646733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244921801761417585180431155 367382702642126377770646733)
            ·
              refine ⟨137768513490797391663992525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 367382702642126377770646733 137768513490797391663992525)
              ·
                refine ⟨51663192559049021873997197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137768513490797391663992525 51663192559049021873997197)
                ·
                  refine ⟨19373697209643383202748949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51663192559049021873997197 19373697209643383202748949)
                  ·
                    refine ⟨908142056702033587628857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19373697209643383202748949 908142056702033587628857)
                    ·
                      rfl

theorem cell23_5305801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 6].length) (baseStart_5305801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305801 prefixEnd_5305801 := by exact prefixLift 5305801
  have htrace : WordTrace (prefixWord ++ tailWord_5305801) baseStart_5305801 baseEnd_5305801 := by
    simpa [prefixWord, tailWord_5305801, baseEnd_5305801] using wordTrace_append hprefix tailTrace_5305801
  have hstable : (prefixWord ++ tailWord_5305801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305801).length < 2 ^ (prefixWord ++ tailWord_5305801).sum := by decide
  have hdescent : baseEnd_5305801 < baseStart_5305801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305808 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 1, 8, 2]
def baseStart_5305808 : Nat := 118140960795 + 5305808 * 2 ^ 59
def prefixEnd_5305808 : Nat := 4983230072969 + 3 ^ 40 * 5305808 * 2
def baseEnd_5305808 : Nat := 2724429764470682235499039

theorem tailTrace_5305808 : CollatzResearch.WordTrace tailWord_5305808 prefixEnd_5305808 2724429764470682235499039 := by
  unfold tailWord_5305808
  simp only [CollatzResearch.WordTrace]
  refine ⟨96759357980985625354219039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129012477307980833805625385 96759357980985625354219039)
  ·
    refine ⟨145139036971478438031328559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96759357980985625354219039 145139036971478438031328559)
    ·
      refine ⟨217708555457217657046992839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145139036971478438031328559 217708555457217657046992839)
      ·
        refine ⟨326562833185826485570489259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217708555457217657046992839 326562833185826485570489259)
        ·
          refine ⟨489844249778739728355733889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326562833185826485570489259 489844249778739728355733889)
          ·
            refine ⟨367383187334054796266800417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489844249778739728355733889 367383187334054796266800417)
            ·
              refine ⟨275537390500541097200100313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367383187334054796266800417 275537390500541097200100313)
              ·
                refine ⟨206653042875405822900075235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275537390500541097200100313 206653042875405822900075235)
                ·
                  refine ⟨309979564313108734350112853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206653042875405822900075235 309979564313108734350112853)
                  ·
                    refine ⟨3632573019294242980665385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 309979564313108734350112853 3632573019294242980665385)
                    ·
                      refine ⟨2724429764470682235499039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3632573019294242980665385 2724429764470682235499039)
                      ·
                        rfl

theorem cell23_5305808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 8, 2].length) (baseStart_5305808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305808 prefixEnd_5305808 := by exact prefixLift 5305808
  have htrace : WordTrace (prefixWord ++ tailWord_5305808) baseStart_5305808 baseEnd_5305808 := by
    simpa [prefixWord, tailWord_5305808, baseEnd_5305808] using wordTrace_append hprefix tailTrace_5305808
  have hstable : (prefixWord ++ tailWord_5305808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305808).length < 2 ^ (prefixWord ++ tailWord_5305808).sum := by decide
  have hdescent : baseEnd_5305808 < baseStart_5305808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305838 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_5305838 : Nat := 118140960795 + 5305838 * 2 ^ 59
def prefixEnd_5305838 : Nat := 4983230072969 + 3 ^ 40 * 5305838 * 2
def baseEnd_5305838 : Nat := 2724445168890317118123901

theorem tailTrace_5305838 : CollatzResearch.WordTrace tailWord_5305838 prefixEnd_5305838 2724445168890317118123901 := by
  unfold tailWord_5305838
  simp only [CollatzResearch.WordTrace]
  refine ⟨24189976268982820729003771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129013206767908377221353445 24189976268982820729003771)
  ·
    refine ⟨36284964403474231093505657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24189976268982820729003771 36284964403474231093505657)
    ·
      refine ⟨27213723302605673320129243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36284964403474231093505657 27213723302605673320129243)
      ·
        refine ⟨40820584953908509980193865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27213723302605673320129243 40820584953908509980193865)
        ·
          refine ⟨30615438715431382485145399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40820584953908509980193865 30615438715431382485145399)
          ·
            refine ⟨45923158073147073727718099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30615438715431382485145399 45923158073147073727718099)
            ·
              refine ⟨68884737109720610591577149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45923158073147073727718099 68884737109720610591577149)
              ·
                refine ⟨25831776416145228971841431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68884737109720610591577149 25831776416145228971841431)
                ·
                  refine ⟨38747664624217843457762147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25831776416145228971841431 38747664624217843457762147)
                  ·
                    refine ⟨58121496936326765186643221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38747664624217843457762147 58121496936326765186643221)
                    ·
                      refine ⟨2724445168890317118123901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58121496936326765186643221 2724445168890317118123901)
                      ·
                        rfl

theorem cell23_5305838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_5305838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305838 prefixEnd_5305838 := by exact prefixLift 5305838
  have htrace : WordTrace (prefixWord ++ tailWord_5305838) baseStart_5305838 baseEnd_5305838 := by
    simpa [prefixWord, tailWord_5305838, baseEnd_5305838] using wordTrace_append hprefix tailTrace_5305838
  have hstable : (prefixWord ++ tailWord_5305838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305838).length < 2 ^ (prefixWord ++ tailWord_5305838).sum := by decide
  have hdescent : baseEnd_5305838 < baseStart_5305838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305842 : List Nat := [3, 2, 1, 4, 1, 1, 3, 2, 1, 1, 4]
def baseStart_5305842 : Nat := 118140960795 + 5305842 * 2 ^ 59
def prefixEnd_5305842 : Nat := 4983230072969 + 3 ^ 40 * 5305842 * 2
def baseEnd_5305842 : Nat := 2724447222812935102473883

theorem tailTrace_5305842 : CollatzResearch.WordTrace tailWord_5305842 prefixEnd_5305842 2724447222812935102473883 := by
  unfold tailWord_5305842
  simp only [CollatzResearch.WordTrace]
  refine ⟨48379989010962018628793945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129013304029232049676783853 48379989010962018628793945)
  ·
    refine ⟨36284991758221513971595459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48379989010962018628793945 36284991758221513971595459)
    ·
      refine ⟨54427487637332270957393189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36284991758221513971595459 54427487637332270957393189)
      ·
        refine ⟨10205153931999800804511223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54427487637332270957393189 10205153931999800804511223)
        ·
          refine ⟨15307730897999701206766835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10205153931999800804511223 15307730897999701206766835)
          ·
            refine ⟨22961596346999551810150253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15307730897999701206766835 22961596346999551810150253)
            ·
              refine ⟨8610598630124831928806345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22961596346999551810150253 8610598630124831928806345)
              ·
                refine ⟨6457948972593623946604759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8610598630124831928806345 6457948972593623946604759)
                ·
                  refine ⟨9686923458890435919907139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6457948972593623946604759 9686923458890435919907139)
                  ·
                    refine ⟨14530385188335653879860709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9686923458890435919907139 14530385188335653879860709)
                    ·
                      refine ⟨2724447222812935102473883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14530385188335653879860709 2724447222812935102473883)
                      ·
                        rfl

theorem cell23_5305842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_5305842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305842 prefixEnd_5305842 := by exact prefixLift 5305842
  have htrace : WordTrace (prefixWord ++ tailWord_5305842) baseStart_5305842 baseEnd_5305842 := by
    simpa [prefixWord, tailWord_5305842, baseEnd_5305842] using wordTrace_append hprefix tailTrace_5305842
  have hstable : (prefixWord ++ tailWord_5305842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305842).length < 2 ^ (prefixWord ++ tailWord_5305842).sum := by decide
  have hdescent : baseEnd_5305842 < baseStart_5305842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305851 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 6]
def baseStart_5305851 : Nat := 118140960795 + 5305851 * 2 ^ 59
def prefixEnd_5305851 : Nat := 4983230072969 + 3 ^ 40 * 5305851 * 2
def baseEnd_5305851 : Nat := 2724451844138825567261341

theorem tailTrace_5305851 : CollatzResearch.WordTrace tailWord_5305851 prefixEnd_5305851 2724451844138825567261341 := by
  unfold tailWord_5305851
  simp only [CollatzResearch.WordTrace]
  refine ⟨193520284300815469052253407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129013522867210312701502271 193520284300815469052253407)
  ·
    refine ⟨290280426451223203578380111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193520284300815469052253407 290280426451223203578380111)
    ·
      refine ⟨435420639676834805367570167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290280426451223203578380111 435420639676834805367570167)
      ·
        refine ⟨653130959515252208051355251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435420639676834805367570167 653130959515252208051355251)
        ·
          refine ⟨979696439272878312077032877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653130959515252208051355251 979696439272878312077032877)
          ·
            refine ⟨367386164727329367028887329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 979696439272878312077032877 367386164727329367028887329)
            ·
              refine ⟨275539623545497025271665497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367386164727329367028887329 275539623545497025271665497)
              ·
                refine ⟨206654717659122768953749123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275539623545497025271665497 206654717659122768953749123)
                ·
                  refine ⟨309982076488684153430623685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206654717659122768953749123 309982076488684153430623685)
                  ·
                    refine ⟨58121639341628278768241941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 309982076488684153430623685 58121639341628278768241941)
                    ·
                      refine ⟨2724451844138825567261341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58121639341628278768241941 2724451844138825567261341)
                      ·
                        rfl

theorem cell23_5305851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 6].length) (baseStart_5305851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305851 prefixEnd_5305851 := by exact prefixLift 5305851
  have htrace : WordTrace (prefixWord ++ tailWord_5305851) baseStart_5305851 baseEnd_5305851 := by
    simpa [prefixWord, tailWord_5305851, baseEnd_5305851] using wordTrace_append hprefix tailTrace_5305851
  have hstable : (prefixWord ++ tailWord_5305851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305851).length < 2 ^ (prefixWord ++ tailWord_5305851).sum := by decide
  have hdescent : baseEnd_5305851 < baseStart_5305851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305886 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_5305886 : Nat := 118140960795 + 5305886 * 2 ^ 59
def prefixEnd_5305886 : Nat := 4983230072969 + 3 ^ 40 * 5305886 * 2
def baseEnd_5305886 : Nat := 908156605320577643441227

theorem tailTrace_5305886 : CollatzResearch.WordTrace tailWord_5305886 prefixEnd_5305886 908156605320577643441227 := by
  unfold tailWord_5305886
  simp only [CollatzResearch.WordTrace]
  refine ⟨24190195106961083753722189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129014373903792446686518341 24190195106961083753722189)
  ·
    refine ⟨9071323165110406407645821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24190195106961083753722189 9071323165110406407645821)
    ·
      refine ⟨3401746186916402402867183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9071323165110406407645821 3401746186916402402867183)
      ·
        refine ⟨5102619280374603604300775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3401746186916402402867183 5102619280374603604300775)
        ·
          refine ⟨7653928920561905406451163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5102619280374603604300775 7653928920561905406451163)
          ·
            refine ⟨11480893380842858109676745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7653928920561905406451163 11480893380842858109676745)
            ·
              refine ⟨8610670035632143582257559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11480893380842858109676745 8610670035632143582257559)
              ·
                refine ⟨12916005053448215373386339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8610670035632143582257559 12916005053448215373386339)
                ·
                  refine ⟨19374007580172323060079509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12916005053448215373386339 19374007580172323060079509)
                  ·
                    refine ⟨908156605320577643441227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19374007580172323060079509 908156605320577643441227)
                    ·
                      rfl

theorem cell23_5305886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_5305886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305886 prefixEnd_5305886 := by exact prefixLift 5305886
  have htrace : WordTrace (prefixWord ++ tailWord_5305886) baseStart_5305886 baseEnd_5305886 := by
    simpa [prefixWord, tailWord_5305886, baseEnd_5305886] using wordTrace_append hprefix tailTrace_5305886
  have hstable : (prefixWord ++ tailWord_5305886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305886).length < 2 ^ (prefixWord ++ tailWord_5305886).sum := by decide
  have hdescent : baseEnd_5305886 < baseStart_5305886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305919 : List Nat := [1, 1, 2, 2, 3, 3, 4, 1, 1, 3, 2]
def baseStart_5305919 : Nat := 118140960795 + 5305919 * 2 ^ 59
def prefixEnd_5305919 : Nat := 4983230072969 + 3 ^ 40 * 5305919 * 2
def baseEnd_5305919 : Nat := 2724486760823331301211029

theorem tailTrace_5305919 : CollatzResearch.WordTrace tailWord_5305919 prefixEnd_5305919 2724486760823331301211029 := by
  unfold tailWord_5305919
  simp only [CollatzResearch.WordTrace]
  refine ⟨193522764464569116665728811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129015176309712744443819207 193522764464569116665728811)
  ·
    refine ⟨290284146696853674998593217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193522764464569116665728811 290284146696853674998593217)
    ·
      refine ⟨217713110022640256248944913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290284146696853674998593217 217713110022640256248944913)
      ·
        refine ⟨163284832516980192186708685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217713110022640256248944913 163284832516980192186708685)
        ·
          refine ⟨61231812193867572070015757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163284832516980192186708685 61231812193867572070015757)
          ·
            refine ⟨22961929572700339526255909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61231812193867572070015757 22961929572700339526255909)
            ·
              refine ⟨4305361794881313661172983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22961929572700339526255909 4305361794881313661172983)
              ·
                refine ⟨6458042692321970491759475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4305361794881313661172983 6458042692321970491759475)
                ·
                  refine ⟨9687064038482955737639213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6458042692321970491759475 9687064038482955737639213)
                  ·
                    refine ⟨3632649014431108401614705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9687064038482955737639213 3632649014431108401614705)
                    ·
                      refine ⟨2724486760823331301211029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3632649014431108401614705 2724486760823331301211029)
                      ·
                        rfl

theorem cell23_5305919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 1, 3, 2].length) (baseStart_5305919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305919 prefixEnd_5305919 := by exact prefixLift 5305919
  have htrace : WordTrace (prefixWord ++ tailWord_5305919) baseStart_5305919 baseEnd_5305919 := by
    simpa [prefixWord, tailWord_5305919, baseEnd_5305919] using wordTrace_append hprefix tailTrace_5305919
  have hstable : (prefixWord ++ tailWord_5305919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305919).length < 2 ^ (prefixWord ++ tailWord_5305919).sum := by decide
  have hdescent : baseEnd_5305919 < baseStart_5305919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305926 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_5305926 : Nat := 118140960795 + 5305926 * 2 ^ 59
def prefixEnd_5305926 : Nat := 4983230072969 + 3 ^ 40 * 5305926 * 2
def baseEnd_5305926 : Nat := 2724490355187912773823497

theorem tailTrace_5305926 : CollatzResearch.WordTrace tailWord_5305926 prefixEnd_5305926 2724490355187912773823497 := by
  unfold tailWord_5305926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6047594367985742401913551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 129015346517029171240822421 6047594367985742401913551)
  ·
    refine ⟨9071391551978613602870327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6047594367985742401913551 9071391551978613602870327)
    ·
      refine ⟨13607087327967920404305491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9071391551978613602870327 13607087327967920404305491)
      ·
        refine ⟨20410630991951880606458237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13607087327967920404305491 20410630991951880606458237)
        ·
          refine ⟨7653986621981955227421839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20410630991951880606458237 7653986621981955227421839)
          ·
            refine ⟨11480979932972932841132759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7653986621981955227421839 11480979932972932841132759)
            ·
              refine ⟨17221469899459399261699139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11480979932972932841132759 17221469899459399261699139)
              ·
                refine ⟨25832204849189098892548709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17221469899459399261699139 25832204849189098892548709)
                ·
                  refine ⟨4843538409222956042352883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25832204849189098892548709 4843538409222956042352883)
                  ·
                    refine ⟨7265307613834434063529325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4843538409222956042352883 7265307613834434063529325)
                    ·
                      refine ⟨2724490355187912773823497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7265307613834434063529325 2724490355187912773823497)
                      ·
                        rfl

theorem cell23_5305926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_5305926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305926 prefixEnd_5305926 := by exact prefixLift 5305926
  have htrace : WordTrace (prefixWord ++ tailWord_5305926) baseStart_5305926 baseEnd_5305926 := by
    simpa [prefixWord, tailWord_5305926, baseEnd_5305926] using wordTrace_append hprefix tailTrace_5305926
  have hstable : (prefixWord ++ tailWord_5305926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305926).length < 2 ^ (prefixWord ++ tailWord_5305926).sum := by decide
  have hdescent : baseEnd_5305926 < baseStart_5305926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305975 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 1, 7, 2]
def baseStart_5305975 : Nat := 118140960795 + 5305975 * 2 ^ 59
def prefixEnd_5305975 : Nat := 4983230072969 + 3 ^ 40 * 5305975 * 2
def baseEnd_5305975 : Nat := 2724515515739983082110771

theorem tailTrace_5305975 : CollatzResearch.WordTrace tailWord_5305975 prefixEnd_5305975 2724515515739983082110771 := by
  unfold tailWord_5305975
  simp only [CollatzResearch.WordTrace]
  refine ⟨193524806952366238229767379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129016537968244158819844919 193524806952366238229767379)
  ·
    refine ⟨290287210428549357344651069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193524806952366238229767379 290287210428549357344651069)
    ·
      refine ⟨108857703910706009004244151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290287210428549357344651069 108857703910706009004244151)
      ·
        refine ⟨163286555866059013506366227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108857703910706009004244151 163286555866059013506366227)
        ·
          refine ⟨244929833799088520259549341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163286555866059013506366227 244929833799088520259549341)
          ·
            refine ⟨91848687674658195097331003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244929833799088520259549341 91848687674658195097331003)
            ·
              refine ⟨137773031511987292645996505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91848687674658195097331003 137773031511987292645996505)
              ·
                refine ⟨103329773633990469484497379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137773031511987292645996505 103329773633990469484497379)
                ·
                  refine ⟨154994660450985704226746069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103329773633990469484497379 154994660450985704226746069)
                  ·
                    refine ⟨3632687354319977442814361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 154994660450985704226746069 3632687354319977442814361)
                    ·
                      refine ⟨2724515515739983082110771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3632687354319977442814361 2724515515739983082110771)
                      ·
                        rfl

theorem cell23_5305975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 7, 2].length) (baseStart_5305975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305975 prefixEnd_5305975 := by exact prefixLift 5305975
  have htrace : WordTrace (prefixWord ++ tailWord_5305975) baseStart_5305975 baseEnd_5305975 := by
    simpa [prefixWord, tailWord_5305975, baseEnd_5305975] using wordTrace_append hprefix tailTrace_5305975
  have hstable : (prefixWord ++ tailWord_5305975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305975).length < 2 ^ (prefixWord ++ tailWord_5305975).sum := by decide
  have hdescent : baseEnd_5305975 < baseStart_5305975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5305985 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 4, 5]
def baseStart_5305985 : Nat := 118140960795 + 5305985 * 2 ^ 59
def prefixEnd_5305985 : Nat := 4983230072969 + 3 ^ 40 * 5305985 * 2
def baseEnd_5305985 : Nat := 908173550182176014328575

theorem tailTrace_5305985 : CollatzResearch.WordTrace tailWord_5305985 prefixEnd_5305985 908173550182176014328575 := by
  unfold tailWord_5305985
  simp only [CollatzResearch.WordTrace]
  refine ⟨193525171682330009937631409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129016781121553339958420939 193525171682330009937631409)
  ·
    refine ⟨145143878761747507453223557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193525171682330009937631409 145143878761747507453223557)
    ·
      refine ⟨27214477267827657647479417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145143878761747507453223557 27214477267827657647479417)
      ·
        refine ⟨20410857950870743235609563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27214477267827657647479417 20410857950870743235609563)
        ·
          refine ⟨30616286926306114853414345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20410857950870743235609563 30616286926306114853414345)
          ·
            refine ⟨22962215194729586140060759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30616286926306114853414345 22962215194729586140060759)
            ·
              refine ⟨34443322792094379210091139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22962215194729586140060759 34443322792094379210091139)
              ·
                refine ⟨51664984188141568815136709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34443322792094379210091139 51664984188141568815136709)
                ·
                  refine ⟨9687184535276544152838133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51664984188141568815136709 9687184535276544152838133)
                  ·
                    refine ⟨908173550182176014328575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9687184535276544152838133 908173550182176014328575)
                    ·
                      rfl

theorem cell23_5305985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_5305985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5305985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5305985 prefixEnd_5305985 := by exact prefixLift 5305985
  have htrace : WordTrace (prefixWord ++ tailWord_5305985) baseStart_5305985 baseEnd_5305985 := by
    simpa [prefixWord, tailWord_5305985, baseEnd_5305985] using wordTrace_append hprefix tailTrace_5305985
  have hstable : (prefixWord ++ tailWord_5305985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5305985).length < 2 ^ (prefixWord ++ tailWord_5305985).sum := by decide
  have hdescent : baseEnd_5305985 < baseStart_5305985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5305985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306042 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3]
def baseStart_5306042 : Nat := 118140960795 + 5306042 * 2 ^ 59
def prefixEnd_5306042 : Nat := 4983230072969 + 3 ^ 40 * 5306042 * 2
def baseEnd_5306042 : Nat := 2724549918943834319972963

theorem tailTrace_5306042 : CollatzResearch.WordTrace tailWord_5306042 prefixEnd_5306042 2724549918943834319972963 := by
  unfold tailWord_5306042
  simp only [CollatzResearch.WordTrace]
  refine ⟨48381812660780877168114095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129018167095415672448304253 48381812660780877168114095)
  ·
    refine ⟨72572718991171315752171143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48381812660780877168114095 72572718991171315752171143)
    ·
      refine ⟨108859078486756973628256715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72572718991171315752171143 108859078486756973628256715)
      ·
        refine ⟨163288617730135460442385073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108859078486756973628256715 163288617730135460442385073)
        ·
          refine ⟨122466463297601595331788805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163288617730135460442385073 122466463297601595331788805)
          ·
            refine ⟨22962461868300299124710401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122466463297601595331788805 22962461868300299124710401)
            ·
              refine ⟨17221846401225224343532801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22962461868300299124710401 17221846401225224343532801)
              ·
                refine ⟨12916384800918918257649601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17221846401225224343532801 12916384800918918257649601)
                ·
                  refine ⟨9687288600689188693237201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12916384800918918257649601 9687288600689188693237201)
                  ·
                    refine ⟨7265466450516891519927901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9687288600689188693237201 7265466450516891519927901)
                    ·
                      refine ⟨2724549918943834319972963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7265466450516891519927901 2724549918943834319972963)
                      ·
                        rfl

theorem cell23_5306042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_5306042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306042 prefixEnd_5306042 := by exact prefixLift 5306042
  have htrace : WordTrace (prefixWord ++ tailWord_5306042) baseStart_5306042 baseEnd_5306042 := by
    simpa [prefixWord, tailWord_5306042, baseEnd_5306042] using wordTrace_append hprefix tailTrace_5306042
  have hstable : (prefixWord ++ tailWord_5306042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306042).length < 2 ^ (prefixWord ++ tailWord_5306042).sum := by decide
  have hdescent : baseEnd_5306042 < baseStart_5306042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306115 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 5]
def baseStart_5306115 : Nat := 118140960795 + 5306115 * 2 ^ 59
def prefixEnd_5306115 : Nat := 4983230072969 + 3 ^ 40 * 5306115 * 2
def baseEnd_5306115 : Nat := 2724587403031612534360127

theorem tailTrace_5306115 : CollatzResearch.WordTrace tailWord_5306115 prefixEnd_5306115 2724587403031612534360127 := by
  unfold tailWord_5306115
  simp only [CollatzResearch.WordTrace]
  refine ⟨193529913171859042139863799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129019942114572694759909199 193529913171859042139863799)
  ·
    refine ⟨290294869757788563209795699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193529913171859042139863799 290294869757788563209795699)
    ·
      refine ⟨435442304636682844814693549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290294869757788563209795699 435442304636682844814693549)
      ·
        refine ⟨163290864238756066805510081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435442304636682844814693549 163290864238756066805510081)
        ·
          refine ⟨122468148179067050104132561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163290864238756066805510081 122468148179067050104132561)
          ·
            refine ⟨91851111134300287578099421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122468148179067050104132561 91851111134300287578099421)
            ·
              refine ⟨34444166675362607841787283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91851111134300287578099421 34444166675362607841787283)
              ·
                refine ⟨51666250013043911762680925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34444166675362607841787283 51666250013043911762680925)
                ·
                  refine ⟨19374843754891466911005347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51666250013043911762680925 19374843754891466911005347)
                  ·
                    refine ⟨29062265632337200366508021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19374843754891466911005347 29062265632337200366508021)
                    ·
                      refine ⟨2724587403031612534360127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29062265632337200366508021 2724587403031612534360127)
                      ·
                        rfl

theorem cell23_5306115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_5306115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306115 prefixEnd_5306115 := by exact prefixLift 5306115
  have htrace : WordTrace (prefixWord ++ tailWord_5306115) baseStart_5306115 baseEnd_5306115 := by
    simpa [prefixWord, tailWord_5306115, baseEnd_5306115] using wordTrace_append hprefix tailTrace_5306115
  have hstable : (prefixWord ++ tailWord_5306115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306115).length < 2 ^ (prefixWord ++ tailWord_5306115).sum := by decide
  have hdescent : baseEnd_5306115 < baseStart_5306115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306122 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 1, 6]
def baseStart_5306122 : Nat := 118140960795 + 5306122 * 2 ^ 59
def prefixEnd_5306122 : Nat := 4983230072969 + 3 ^ 40 * 5306122 * 2
def baseEnd_5306122 : Nat := 908196999132064668990865

theorem tailTrace_5306122 : CollatzResearch.WordTrace tailWord_5306122 prefixEnd_5306122 908196999132064668990865 := by
  unfold tailWord_5306122
  simp only [CollatzResearch.WordTrace]
  refine ⟨48382542120708420583842155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129020112321889121556912413 48382542120708420583842155)
  ·
    refine ⟨72573813181062630875763233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48382542120708420583842155 72573813181062630875763233)
    ·
      refine ⟨54430359885796973156822425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72573813181062630875763233 54430359885796973156822425)
      ·
        refine ⟨40822769914347729867616819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54430359885796973156822425 40822769914347729867616819)
        ·
          refine ⟨61234154871521594801425229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40822769914347729867616819 61234154871521594801425229)
          ·
            refine ⟨22962808076820598050534461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61234154871521594801425229 22962808076820598050534461)
            ·
              refine ⟨8611053028807724268950423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22962808076820598050534461 8611053028807724268950423)
              ·
                refine ⟨12916579543211586403425635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8611053028807724268950423 12916579543211586403425635)
                ·
                  refine ⟨19374869314817379605138453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12916579543211586403425635 19374869314817379605138453)
                  ·
                    refine ⟨908196999132064668990865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19374869314817379605138453 908196999132064668990865)
                    ·
                      rfl

theorem cell23_5306122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_5306122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306122 prefixEnd_5306122 := by exact prefixLift 5306122
  have htrace : WordTrace (prefixWord ++ tailWord_5306122) baseStart_5306122 baseEnd_5306122 := by
    simpa [prefixWord, tailWord_5306122, baseEnd_5306122] using wordTrace_append hprefix tailTrace_5306122
  have hstable : (prefixWord ++ tailWord_5306122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306122).length < 2 ^ (prefixWord ++ tailWord_5306122).sum := by decide
  have hdescent : baseEnd_5306122 < baseStart_5306122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306149 : List Nat := [1, 3, 1, 2, 3, 2, 2, 3, 1, 2, 3]
def baseStart_5306149 : Nat := 118140960795 + 5306149 * 2 ^ 59
def prefixEnd_5306149 : Nat := 4983230072969 + 3 ^ 40 * 5306149 * 2
def baseEnd_5306149 : Nat := 2724604861373865401334971

theorem tailTrace_5306149 : CollatzResearch.WordTrace tailWord_5306149 prefixEnd_5306149 2724604861373865401334971 := by
  unfold tailWord_5306149
  simp only [CollatzResearch.WordTrace]
  refine ⟨193531153253735865946601501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129020768835823910631067667 193531153253735865946601501)
  ·
    refine ⟨72574182470150949729975563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193531153253735865946601501 72574182470150949729975563)
    ·
      refine ⟨108861273705226424594963345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72574182470150949729975563 108861273705226424594963345)
      ·
        refine ⟨81645955278919818446222509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108861273705226424594963345 81645955278919818446222509)
        ·
          refine ⟨30617233229594931917333441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81645955278919818446222509 30617233229594931917333441)
          ·
            refine ⟨22962924922196198938000081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30617233229594931917333441 22962924922196198938000081)
            ·
              refine ⟨17222193691647149203500061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22962924922196198938000081 17222193691647149203500061)
              ·
                refine ⟨6458322634367680951312523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17222193691647149203500061 6458322634367680951312523)
                ·
                  refine ⟨9687483951551521426968785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6458322634367680951312523 9687483951551521426968785)
                  ·
                    refine ⟨7265612963663641070226589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9687483951551521426968785 7265612963663641070226589)
                    ·
                      refine ⟨2724604861373865401334971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7265612963663641070226589 2724604861373865401334971)
                      ·
                        rfl

theorem cell23_5306149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_5306149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306149 prefixEnd_5306149 := by exact prefixLift 5306149
  have htrace : WordTrace (prefixWord ++ tailWord_5306149) baseStart_5306149 baseEnd_5306149 := by
    simpa [prefixWord, tailWord_5306149, baseEnd_5306149] using wordTrace_append hprefix tailTrace_5306149
  have hstable : (prefixWord ++ tailWord_5306149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306149).length < 2 ^ (prefixWord ++ tailWord_5306149).sum := by decide
  have hdescent : baseEnd_5306149 < baseStart_5306149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306152 : List Nat := [2, 1, 5, 1, 1, 4, 9]
def baseStart_5306152 : Nat := 118140960795 + 5306152 * 2 ^ 59
def prefixEnd_5306152 : Nat := 4983230072969 + 3 ^ 40 * 5306152 * 2
def baseEnd_5306152 : Nat := 33637116071800356661697

theorem tailTrace_5306152 : CollatzResearch.WordTrace tailWord_5306152 prefixEnd_5306152 33637116071800356661697 := by
  unfold tailWord_5306152
  simp only [CollatzResearch.WordTrace]
  refine ⟨96765631336362498729480355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129020841781816664972640473 96765631336362498729480355)
  ·
    refine ⟨145148447004543748094220533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96765631336362498729480355 145148447004543748094220533)
    ·
      refine ⟨13607666906675976383833175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145148447004543748094220533 13607666906675976383833175)
      ·
        refine ⟨20411500360013964575749763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13607666906675976383833175 20411500360013964575749763)
        ·
          refine ⟨30617250540020946863624645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20411500360013964575749763 30617250540020946863624645)
          ·
            refine ⟨5740734476253927536929621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30617250540020946863624645 5740734476253927536929621)
            ·
              refine ⟨33637116071800356661697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5740734476253927536929621 33637116071800356661697)
              ·
                rfl

theorem cell23_5306152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 9].length) (baseStart_5306152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306152 prefixEnd_5306152 := by exact prefixLift 5306152
  have htrace : WordTrace (prefixWord ++ tailWord_5306152) baseStart_5306152 baseEnd_5306152 := by
    simpa [prefixWord, tailWord_5306152, baseEnd_5306152] using wordTrace_append hprefix tailTrace_5306152
  have hstable : (prefixWord ++ tailWord_5306152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306152).length < 2 ^ (prefixWord ++ tailWord_5306152).sum := by decide
  have hdescent : baseEnd_5306152 < baseStart_5306152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306163 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 3, 2, 2]
def baseStart_5306163 : Nat := 118140960795 + 5306163 * 2 ^ 59
def prefixEnd_5306163 : Nat := 4983230072969 + 3 ^ 40 * 5306163 * 2
def baseEnd_5306163 : Nat := 2724612050103028346559907

theorem tailTrace_5306163 : CollatzResearch.WordTrace tailWord_5306163 prefixEnd_5306163 2724612050103028346559907 := by
  unfold tailWord_5306163
  simp only [CollatzResearch.WordTrace]
  refine ⟨193531663875685146337611143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129021109250456764225074095 193531663875685146337611143)
  ·
    refine ⟨290297495813527719506416715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193531663875685146337611143 290297495813527719506416715)
    ·
      refine ⟨435446243720291579259625073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290297495813527719506416715 435446243720291579259625073)
      ·
        refine ⟨326584682790218684444718805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435446243720291579259625073 326584682790218684444718805)
        ·
          refine ⟨7654328502895750416673097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 326584682790218684444718805 7654328502895750416673097)
          ·
            refine ⟨5740746377171812812504823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7654328502895750416673097 5740746377171812812504823)
            ·
              refine ⟨8611119565757719218757235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5740746377171812812504823 8611119565757719218757235)
              ·
                refine ⟨12916679348636578828135853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8611119565757719218757235 12916679348636578828135853)
                ·
                  refine ⟨4843754755738717060550945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12916679348636578828135853 4843754755738717060550945)
                  ·
                    refine ⟨3632816066804037795413209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4843754755738717060550945 3632816066804037795413209)
                    ·
                      refine ⟨2724612050103028346559907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3632816066804037795413209 2724612050103028346559907)
                      ·
                        rfl

theorem cell23_5306163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 2, 2].length) (baseStart_5306163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306163 prefixEnd_5306163 := by exact prefixLift 5306163
  have htrace : WordTrace (prefixWord ++ tailWord_5306163) baseStart_5306163 baseEnd_5306163 := by
    simpa [prefixWord, tailWord_5306163, baseEnd_5306163] using wordTrace_append hprefix tailTrace_5306163
  have hstable : (prefixWord ++ tailWord_5306163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306163).length < 2 ^ (prefixWord ++ tailWord_5306163).sum := by decide
  have hdescent : baseEnd_5306163 < baseStart_5306163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306169 : List Nat := [1, 2, 1, 7, 1, 1, 2, 8]
def baseStart_5306169 : Nat := 118140960795 + 5306169 * 2 ^ 59
def prefixEnd_5306169 : Nat := 4983230072969 + 3 ^ 40 * 5306169 * 2
def baseEnd_5306169 : Nat := 100911671518035382336477

theorem tailTrace_5306169 : CollatzResearch.WordTrace tailWord_5306169 prefixEnd_5306169 100911671518035382336477 := by
  unfold tailWord_5306169
  simp only [CollatzResearch.WordTrace]
  refine ⟨193531882713663409362329561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129021255142442272908219707 193531882713663409362329561)
  ·
    refine ⟨145148912035247557021747171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193531882713663409362329561 145148912035247557021747171)
    ·
      refine ⟨217723368052871335532620757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145148912035247557021747171 217723368052871335532620757)
      ·
        refine ⟨5102891438739171926545799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 217723368052871335532620757 5102891438739171926545799)
        ·
          refine ⟨7654337158108757889818699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5102891438739171926545799 7654337158108757889818699)
          ·
            refine ⟨11481505737163136834728049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7654337158108757889818699 11481505737163136834728049)
            ·
              refine ⟨8611129302872352626046037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11481505737163136834728049 8611129302872352626046037)
              ·
                refine ⟨100911671518035382336477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8611129302872352626046037 100911671518035382336477)
                ·
                  rfl

theorem cell23_5306169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 8].length) (baseStart_5306169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306169 prefixEnd_5306169 := by exact prefixLift 5306169
  have htrace : WordTrace (prefixWord ++ tailWord_5306169) baseStart_5306169 baseEnd_5306169 := by
    simpa [prefixWord, tailWord_5306169, baseEnd_5306169] using wordTrace_append hprefix tailTrace_5306169
  have hstable : (prefixWord ++ tailWord_5306169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306169).length < 2 ^ (prefixWord ++ tailWord_5306169).sum := by decide
  have hdescent : baseEnd_5306169 < baseStart_5306169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306173 : List Nat := [1, 4, 1, 4, 1, 3, 2, 1, 2, 4]
def baseStart_5306173 : Nat := 118140960795 + 5306173 * 2 ^ 59
def prefixEnd_5306173 : Nat := 4983230072969 + 3 ^ 40 * 5306173 * 2
def baseEnd_5306173 : Nat := 908205728303191102478287

theorem tailTrace_5306173 : CollatzResearch.WordTrace tailWord_5306173 prefixEnd_5306173 908205728303191102478287 := by
  unfold tailWord_5306173
  simp only [CollatzResearch.WordTrace]
  refine ⟨193532028605648918045475173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129021352403765945363650115 193532028605648918045475173)
  ·
    refine ⟨36287255363559172133526595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193532028605648918045475173 36287255363559172133526595)
    ·
      refine ⟨54430883045338758200289893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36287255363559172133526595 54430883045338758200289893)
      ·
        refine ⟨10205790571001017162554355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54430883045338758200289893 10205790571001017162554355)
        ·
          refine ⟨15308685856501525743831533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10205790571001017162554355 15308685856501525743831533)
          ·
            refine ⟨5740757196188072153936825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15308685856501525743831533 5740757196188072153936825)
            ·
              refine ⟨4305567897141054115452619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5740757196188072153936825 4305567897141054115452619)
              ·
                refine ⟨6458351845711581173178929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4305567897141054115452619 6458351845711581173178929)
                ·
                  refine ⟨4843763884283685879884197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6458351845711581173178929 4843763884283685879884197)
                  ·
                    refine ⟨908205728303191102478287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4843763884283685879884197 908205728303191102478287)
                    ·
                      rfl

theorem cell23_5306173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_5306173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306173 prefixEnd_5306173 := by exact prefixLift 5306173
  have htrace : WordTrace (prefixWord ++ tailWord_5306173) baseStart_5306173 baseEnd_5306173 := by
    simpa [prefixWord, tailWord_5306173, baseEnd_5306173] using wordTrace_append hprefix tailTrace_5306173
  have hstable : (prefixWord ++ tailWord_5306173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306173).length < 2 ^ (prefixWord ++ tailWord_5306173).sum := by decide
  have hdescent : baseEnd_5306173 < baseStart_5306173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306195 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 6, 6]
def baseStart_5306195 : Nat := 118140960795 + 5306195 * 2 ^ 59
def prefixEnd_5306195 : Nat := 4983230072969 + 3 ^ 40 * 5306195 * 2
def baseEnd_5306195 : Nat := 908209493827990740453253

theorem tailTrace_5306195 : CollatzResearch.WordTrace tailWord_5306195 prefixEnd_5306195 908209493827990740453253 := by
  unfold tailWord_5306195
  simp only [CollatzResearch.WordTrace]
  refine ⟨193532831011569215802776039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129021887341046143868517359 193532831011569215802776039)
  ·
    refine ⟨290299246517353823704164059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193532831011569215802776039 290299246517353823704164059)
    ·
      refine ⟨435448869776030735556246089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290299246517353823704164059 435448869776030735556246089)
      ·
        refine ⟨326586652332023051667184567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435448869776030735556246089 326586652332023051667184567)
        ·
          refine ⟨489879978498034577500776851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326586652332023051667184567 489879978498034577500776851)
          ·
            refine ⟨734819967747051866251165277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489879978498034577500776851 734819967747051866251165277)
            ·
              refine ⟨275557487905144449844186979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 734819967747051866251165277 275557487905144449844186979)
              ·
                refine ⟨413336231857716674766280469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275557487905144449844186979 413336231857716674766280469)
                ·
                  refine ⟨19375135868330469129669397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 413336231857716674766280469 19375135868330469129669397)
                  ·
                    refine ⟨908209493827990740453253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19375135868330469129669397 908209493827990740453253)
                    ·
                      rfl

theorem cell23_5306195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 6].length) (baseStart_5306195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306195 prefixEnd_5306195 := by exact prefixLift 5306195
  have htrace : WordTrace (prefixWord ++ tailWord_5306195) baseStart_5306195 baseEnd_5306195 := by
    simpa [prefixWord, tailWord_5306195, baseEnd_5306195] using wordTrace_append hprefix tailTrace_5306195
  have hstable : (prefixWord ++ tailWord_5306195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306195).length < 2 ^ (prefixWord ++ tailWord_5306195).sum := by decide
  have hdescent : baseEnd_5306195 < baseStart_5306195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306252 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 3, 5, 3]
def baseStart_5306252 : Nat := 118140960795 + 5306252 * 2 ^ 59
def prefixEnd_5306252 : Nat := 4983230072969 + 3 ^ 40 * 5306252 * 2
def baseEnd_5306252 : Nat := 2724657749881278498346997

theorem tailTrace_5306252 : CollatzResearch.WordTrace tailWord_5306252 prefixEnd_5306252 2724657749881278498346997 := by
  unfold tailWord_5306252
  simp only [CollatzResearch.WordTrace]
  refine ⟨96767454986181357268800505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129023273314908476358400673 96767454986181357268800505)
  ·
    refine ⟨72575591239636017951600379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96767454986181357268800505 72575591239636017951600379)
    ·
      refine ⟨108863386859454026927400569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72575591239636017951600379 108863386859454026927400569)
      ·
        refine ⟨81647540144590520195550427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108863386859454026927400569 81647540144590520195550427)
        ·
          refine ⟨122471310216885780293325641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81647540144590520195550427 122471310216885780293325641)
          ·
            refine ⟨91853482662664335219994231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122471310216885780293325641 91853482662664335219994231)
            ·
              refine ⟨137780223993996502829991347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91853482662664335219994231 137780223993996502829991347)
              ·
                refine ⟨206670335990994754244987021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137780223993996502829991347 206670335990994754244987021)
                ·
                  refine ⟨77501375996623032841870133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206670335990994754244987021 77501375996623032841870133)
                  ·
                    refine ⟨7265753999683409328925325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77501375996623032841870133 7265753999683409328925325)
                    ·
                      refine ⟨2724657749881278498346997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7265753999683409328925325 2724657749881278498346997)
                      ·
                        rfl

theorem cell23_5306252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_5306252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306252 prefixEnd_5306252 := by exact prefixLift 5306252
  have htrace : WordTrace (prefixWord ++ tailWord_5306252) baseStart_5306252 baseEnd_5306252 := by
    simpa [prefixWord, tailWord_5306252, baseEnd_5306252] using wordTrace_append hprefix tailTrace_5306252
  have hstable : (prefixWord ++ tailWord_5306252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306252).length < 2 ^ (prefixWord ++ tailWord_5306252).sum := by decide
  have hdescent : baseEnd_5306252 < baseStart_5306252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306269 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_5306269 : Nat := 118140960795 + 5306269 * 2 ^ 59
def prefixEnd_5306269 : Nat := 4983230072969 + 3 ^ 40 * 5306269 * 2
def baseEnd_5306269 : Nat := 2724666479052404931834419

theorem tailTrace_5306269 : CollatzResearch.WordTrace tailWord_5306269 prefixEnd_5306269 2724666479052404931834419 := by
  unfold tailWord_5306269
  simp only [CollatzResearch.WordTrace]
  refine ⟨193535530013301126440969861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129023686675534084293979907 193535530013301126440969861)
  ·
    refine ⟨36287911877493961207681849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193535530013301126440969861 36287911877493961207681849)
    ·
      refine ⟨27215933908120470905761387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36287911877493961207681849 27215933908120470905761387)
      ·
        refine ⟨40823900862180706358642081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27215933908120470905761387 40823900862180706358642081)
        ·
          refine ⟨30617925646635529768981561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40823900862180706358642081 30617925646635529768981561)
          ·
            refine ⟨22963444234976647326736171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30617925646635529768981561 22963444234976647326736171)
            ·
              refine ⟨34445166352464970990104257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22963444234976647326736171 34445166352464970990104257)
              ·
                refine ⟨25833874764348728242578193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34445166352464970990104257 25833874764348728242578193)
                ·
                  refine ⟨19375406073261546181933645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25833874764348728242578193 19375406073261546181933645)
                  ·
                    refine ⟨7265777277473079818225117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19375406073261546181933645 7265777277473079818225117)
                    ·
                      refine ⟨2724666479052404931834419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7265777277473079818225117 2724666479052404931834419)
                      ·
                        rfl

theorem cell23_5306269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_5306269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306269 prefixEnd_5306269 := by exact prefixLift 5306269
  have htrace : WordTrace (prefixWord ++ tailWord_5306269) baseStart_5306269 baseEnd_5306269 := by
    simpa [prefixWord, tailWord_5306269, baseEnd_5306269] using wordTrace_append hprefix tailTrace_5306269
  have hstable : (prefixWord ++ tailWord_5306269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306269).length < 2 ^ (prefixWord ++ tailWord_5306269).sum := by decide
  have hdescent : baseEnd_5306269 < baseStart_5306269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306272 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 4, 5]
def baseStart_5306272 : Nat := 118140960795 + 5306272 * 2 ^ 59
def prefixEnd_5306272 : Nat := 4983230072969 + 3 ^ 40 * 5306272 * 2
def baseEnd_5306272 : Nat := 908222673164789473365635

theorem tailTrace_5306272 : CollatzResearch.WordTrace tailWord_5306272 prefixEnd_5306272 908222673164789473365635 := by
  unfold tailWord_5306272
  simp only [CollatzResearch.WordTrace]
  refine ⟨96767819716145128976664535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129023759621526838635552713 96767819716145128976664535)
  ·
    refine ⟨145151729574217693464996803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96767819716145128976664535 145151729574217693464996803)
    ·
      refine ⟨217727594361326540197495205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145151729574217693464996803 217727594361326540197495205)
      ·
        refine ⟨40823923942748726287030351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217727594361326540197495205 40823923942748726287030351)
        ·
          refine ⟨61235885914123089430545527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40823923942748726287030351 61235885914123089430545527)
          ·
            refine ⟨91853828871184634145818291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61235885914123089430545527 91853828871184634145818291)
            ·
              refine ⟨137780743306776951218727437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91853828871184634145818291 137780743306776951218727437)
              ·
                refine ⟨51667778740041356707022789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137780743306776951218727437 51667778740041356707022789)
                ·
                  refine ⟨9687708513757754382566773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51667778740041356707022789 9687708513757754382566773)
                  ·
                    refine ⟨908222673164789473365635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9687708513757754382566773 908222673164789473365635)
                    ·
                      rfl

theorem cell23_5306272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 4, 5].length) (baseStart_5306272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306272 prefixEnd_5306272 := by exact prefixLift 5306272
  have htrace : WordTrace (prefixWord ++ tailWord_5306272) baseStart_5306272 baseEnd_5306272 := by
    simpa [prefixWord, tailWord_5306272, baseEnd_5306272] using wordTrace_append hprefix tailTrace_5306272
  have hstable : (prefixWord ++ tailWord_5306272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306272).length < 2 ^ (prefixWord ++ tailWord_5306272).sum := by decide
  have hdescent : baseEnd_5306272 < baseStart_5306272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306309 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 4, 4, 2]
def baseStart_5306309 : Nat := 118140960795 + 5306309 * 2 ^ 59
def prefixEnd_5306309 : Nat := 4983230072969 + 3 ^ 40 * 5306309 * 2
def baseEnd_5306309 : Nat := 2724687018278584775334235

theorem tailTrace_5306309 : CollatzResearch.WordTrace tailWord_5306309 prefixEnd_5306309 2724687018278584775334235 := by
  unfold tailWord_5306309
  simp only [CollatzResearch.WordTrace]
  refine ⟨193536988933156213272425981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129024659288770808848283987 193536988933156213272425981)
  ·
    refine ⟨72576370849933579977159743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193536988933156213272425981 72576370849933579977159743)
    ·
      refine ⟨108864556274900369965739615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72576370849933579977159743 108864556274900369965739615)
      ·
        refine ⟨163296834412350554948609423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108864556274900369965739615 163296834412350554948609423)
        ·
          refine ⟨244945251618525832422914135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163296834412350554948609423 244945251618525832422914135)
          ·
            refine ⟨367417877427788748634371203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244945251618525832422914135 367417877427788748634371203)
            ·
              refine ⟨551126816141683122951556805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367417877427788748634371203 551126816141683122951556805)
              ·
                refine ⟨103336278026565585553416901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 551126816141683122951556805 103336278026565585553416901)
                ·
                  refine ⟨19375552129981047291265669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103336278026565585553416901 19375552129981047291265669)
                  ·
                    refine ⟨3632916024371446367112313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19375552129981047291265669 3632916024371446367112313)
                    ·
                      refine ⟨2724687018278584775334235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3632916024371446367112313 2724687018278584775334235)
                      ·
                        rfl

theorem cell23_5306309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 4, 2].length) (baseStart_5306309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306309 prefixEnd_5306309 := by exact prefixLift 5306309
  have htrace : WordTrace (prefixWord ++ tailWord_5306309) baseStart_5306309 baseEnd_5306309 := by
    simpa [prefixWord, tailWord_5306309, baseEnd_5306309] using wordTrace_append hprefix tailTrace_5306309
  have hstable : (prefixWord ++ tailWord_5306309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306309).length < 2 ^ (prefixWord ++ tailWord_5306309).sum := by decide
  have hdescent : baseEnd_5306309 < baseStart_5306309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306336 : List Nat := [2, 1, 1, 3, 1, 1, 1, 8, 1, 4]
def baseStart_5306336 : Nat := 118140960795 + 5306336 * 2 ^ 59
def prefixEnd_5306336 : Nat := 4983230072969 + 3 ^ 40 * 5306336 * 2
def baseEnd_5306336 : Nat := 908233627418752056565537

theorem tailTrace_5306336 : CollatzResearch.WordTrace tailWord_5306336 prefixEnd_5306336 908233627418752056565537 := by
  unfold tailWord_5306336
  simp only [CollatzResearch.WordTrace]
  refine ⟨96768986852029198441829431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129025315802705597922439241 96768986852029198441829431)
  ·
    refine ⟨145153480278043797662744147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96768986852029198441829431 145153480278043797662744147)
    ·
      refine ⟨217730220417065696494116221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145153480278043797662744147 217730220417065696494116221)
      ·
        refine ⟨81648832656399636185293583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217730220417065696494116221 81648832656399636185293583)
        ·
          refine ⟨122473248984599454277940375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81648832656399636185293583 122473248984599454277940375)
          ·
            refine ⟨183709873476899181416910563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122473248984599454277940375 183709873476899181416910563)
            ·
              refine ⟨275564810215348772125365845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183709873476899181416910563 275564810215348772125365845)
              ·
                refine ⟨3229275119711118423344131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 275564810215348772125365845 3229275119711118423344131)
                ·
                  refine ⟨4843912679566677635016197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3229275119711118423344131 4843912679566677635016197)
                  ·
                    refine ⟨908233627418752056565537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4843912679566677635016197 908233627418752056565537)
                    ·
                      rfl

theorem cell23_5306336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 8, 1, 4].length) (baseStart_5306336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306336 prefixEnd_5306336 := by exact prefixLift 5306336
  have htrace : WordTrace (prefixWord ++ tailWord_5306336) baseStart_5306336 baseEnd_5306336 := by
    simpa [prefixWord, tailWord_5306336, baseEnd_5306336] using wordTrace_append hprefix tailTrace_5306336
  have hstable : (prefixWord ++ tailWord_5306336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306336).length < 2 ^ (prefixWord ++ tailWord_5306336).sum := by decide
  have hdescent : baseEnd_5306336 < baseStart_5306336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306352 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 6]
def baseStart_5306352 : Nat := 118140960795 + 5306352 * 2 ^ 59
def prefixEnd_5306352 : Nat := 4983230072969 + 3 ^ 40 * 5306352 * 2
def baseEnd_5306352 : Nat := 2724709097946728107096537

theorem tailTrace_5306352 : CollatzResearch.WordTrace tailWord_5306352 prefixEnd_5306352 2724709097946728107096537 := by
  unfold tailWord_5306352
  simp only [CollatzResearch.WordTrace]
  refine ⟨96769278636000215808120655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129025704848000287744160873 96769278636000215808120655)
  ·
    refine ⟨145153917954000323712180983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96769278636000215808120655 145153917954000323712180983)
    ·
      refine ⟨217730876931000485568271475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145153917954000323712180983 217730876931000485568271475)
      ·
        refine ⟨326596315396500728352407213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217730876931000485568271475 326596315396500728352407213)
        ·
          refine ⟨122473618273687773132152705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326596315396500728352407213 122473618273687773132152705)
          ·
            refine ⟨91855213705265829849114529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122473618273687773132152705 91855213705265829849114529)
            ·
              refine ⟨68891410278949372386835897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91855213705265829849114529 68891410278949372386835897)
              ·
                refine ⟨51668557709212029290126923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68891410278949372386835897 51668557709212029290126923)
                ·
                  refine ⟨77502836563818043935190385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51668557709212029290126923 77502836563818043935190385)
                  ·
                    refine ⟨58127127422863532951392789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77502836563818043935190385 58127127422863532951392789)
                    ·
                      refine ⟨2724709097946728107096537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58127127422863532951392789 2724709097946728107096537)
                      ·
                        rfl

theorem cell23_5306352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_5306352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306352 prefixEnd_5306352 := by exact prefixLift 5306352
  have htrace : WordTrace (prefixWord ++ tailWord_5306352) baseStart_5306352 baseEnd_5306352 := by
    simpa [prefixWord, tailWord_5306352, baseEnd_5306352] using wordTrace_append hprefix tailTrace_5306352
  have hstable : (prefixWord ++ tailWord_5306352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306352).length < 2 ^ (prefixWord ++ tailWord_5306352).sum := by decide
  have hdescent : baseEnd_5306352 < baseStart_5306352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306399 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 4]
def baseStart_5306399 : Nat := 118140960795 + 5306399 * 2 ^ 59
def prefixEnd_5306399 : Nat := 4983230072969 + 3 ^ 40 * 5306399 * 2
def baseEnd_5306399 : Nat := 2724733231537489423208821

theorem tailTrace_5306399 : CollatzResearch.WordTrace tailWord_5306399 prefixEnd_5306399 2724733231537489423208821 := by
  unfold tailWord_5306399
  simp only [CollatzResearch.WordTrace]
  refine ⟨193540271502830158643202251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129026847668553439095468167 193540271502830158643202251)
  ·
    refine ⟨290310407254245237964803377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193540271502830158643202251 290310407254245237964803377)
    ·
      refine ⟨217732805440683928473602533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290310407254245237964803377 217732805440683928473602533)
      ·
        refine ⟨40824901020128236588800475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217732805440683928473602533 40824901020128236588800475)
        ·
          refine ⟨61237351530192354883200713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40824901020128236588800475 61237351530192354883200713)
          ·
            refine ⟨45928013647644266162400535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61237351530192354883200713 45928013647644266162400535)
            ·
              refine ⟨68892020471466399243600803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45928013647644266162400535 68892020471466399243600803)
              ·
                refine ⟨103338030707199598865401205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68892020471466399243600803 103338030707199598865401205)
                ·
                  refine ⟨9687940378799962393631363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103338030707199598865401205 9687940378799962393631363)
                  ·
                    refine ⟨14531910568199943590447045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9687940378799962393631363 14531910568199943590447045)
                    ·
                      refine ⟨2724733231537489423208821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14531910568199943590447045 2724733231537489423208821)
                      ·
                        rfl

theorem cell23_5306399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_5306399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306399 prefixEnd_5306399 := by exact prefixLift 5306399
  have htrace : WordTrace (prefixWord ++ tailWord_5306399) baseStart_5306399 baseEnd_5306399 := by
    simpa [prefixWord, tailWord_5306399, baseEnd_5306399] using wordTrace_append hprefix tailTrace_5306399
  have hstable : (prefixWord ++ tailWord_5306399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306399).length < 2 ^ (prefixWord ++ tailWord_5306399).sum := by decide
  have hdescent : baseEnd_5306399 < baseStart_5306399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306420 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_5306420 : Nat := 118140960795 + 5306420 * 2 ^ 59
def prefixEnd_5306420 : Nat := 4983230072969 + 3 ^ 40 * 5306420 * 2
def baseEnd_5306420 : Nat := 2724744014631233841046225

theorem tailTrace_5306420 : CollatzResearch.WordTrace tailWord_5306420 prefixEnd_5306420 2724744014631233841046225 := by
  unfold tailWord_5306420
  simp only [CollatzResearch.WordTrace]
  refine ⟨96770518717877039614858357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129027358290502719486477809 96770518717877039614858357)
  ·
    refine ⟨9072236129800972463892971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96770518717877039614858357 9072236129800972463892971)
    ·
      refine ⟨13608354194701458695839457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9072236129800972463892971 13608354194701458695839457)
      ·
        refine ⟨10206265646026094021879593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13608354194701458695839457 10206265646026094021879593)
        ·
          refine ⟨7654699234519570516409695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10206265646026094021879593 7654699234519570516409695)
          ·
            refine ⟨11482048851779355774614543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7654699234519570516409695 11482048851779355774614543)
            ·
              refine ⟨17223073277669033661921815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11482048851779355774614543 17223073277669033661921815)
              ·
                refine ⟨25834609916503550492882723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17223073277669033661921815 25834609916503550492882723)
                ·
                  refine ⟨38751914874755325739324085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25834609916503550492882723 38751914874755325739324085)
                  ·
                    refine ⟨3632992019508311788061633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38751914874755325739324085 3632992019508311788061633)
                    ·
                      refine ⟨2724744014631233841046225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3632992019508311788061633 2724744014631233841046225)
                      ·
                        rfl

theorem cell23_5306420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_5306420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306420 prefixEnd_5306420 := by exact prefixLift 5306420
  have htrace : WordTrace (prefixWord ++ tailWord_5306420) baseStart_5306420 baseEnd_5306420 := by
    simpa [prefixWord, tailWord_5306420, baseEnd_5306420] using wordTrace_append hprefix tailTrace_5306420
  have hstable : (prefixWord ++ tailWord_5306420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306420).length < 2 ^ (prefixWord ++ tailWord_5306420).sum := by decide
  have hdescent : baseEnd_5306420 < baseStart_5306420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306433 : List Nat := [1, 2, 5, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_5306433 : Nat := 118140960795 + 5306433 * 2 ^ 59
def prefixEnd_5306433 : Nat := 4983230072969 + 3 ^ 40 * 5306433 * 2
def baseEnd_5306433 : Nat := 2724750689879742290183665

theorem tailTrace_5306433 : CollatzResearch.WordTrace tailWord_5306433 prefixEnd_5306433 2724750689879742290183665 := by
  unfold tailWord_5306433
  simp only [CollatzResearch.WordTrace]
  refine ⟨193541511584706982449939953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129027674389804654966626635 193541511584706982449939953)
  ·
    refine ⟨145156133688530236837454965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193541511584706982449939953 145156133688530236837454965)
    ·
      refine ⟨13608387533299709703511403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145156133688530236837454965 13608387533299709703511403)
      ·
        refine ⟨20412581299949564555267105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13608387533299709703511403 20412581299949564555267105)
        ·
          refine ⟨15309435974962173416450329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20412581299949564555267105 15309435974962173416450329)
          ·
            refine ⟨11482076981221630062337747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15309435974962173416450329 11482076981221630062337747)
            ·
              refine ⟨17223115471832445093506621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11482076981221630062337747 17223115471832445093506621)
              ·
                refine ⟨6458668301937166910064983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17223115471832445093506621 6458668301937166910064983)
                ·
                  refine ⟨9688002452905750365097475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6458668301937166910064983 9688002452905750365097475)
                  ·
                    refine ⟨14532003679358625547646213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9688002452905750365097475 14532003679358625547646213)
                    ·
                      refine ⟨2724750689879742290183665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14532003679358625547646213 2724750689879742290183665)
                      ·
                        rfl

theorem cell23_5306433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_5306433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306433 prefixEnd_5306433 := by exact prefixLift 5306433
  have htrace : WordTrace (prefixWord ++ tailWord_5306433) baseStart_5306433 baseEnd_5306433 := by
    simpa [prefixWord, tailWord_5306433, baseEnd_5306433] using wordTrace_append hprefix tailTrace_5306433
  have hstable : (prefixWord ++ tailWord_5306433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306433).length < 2 ^ (prefixWord ++ tailWord_5306433).sum := by decide
  have hdescent : baseEnd_5306433 < baseStart_5306433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306460 : List Nat := [2, 2, 4, 1, 1, 3, 3, 1, 2, 4]
def baseStart_5306460 : Nat := 118140960795 + 5306460 * 2 ^ 59
def prefixEnd_5306460 : Nat := 4983230072969 + 3 ^ 40 * 5306460 * 2
def baseEnd_5306460 : Nat := 908254851285804561515347

theorem tailTrace_5306460 : CollatzResearch.WordTrace tailWord_5306460 prefixEnd_5306460 908254851285804561515347 := by
  unfold tailWord_5306460
  simp only [CollatzResearch.WordTrace]
  refine ⟨96771248177804583030586417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129028330903739444040781889 96771248177804583030586417)
  ·
    refine ⟨72578436133353437272939813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96771248177804583030586417 72578436133353437272939813)
    ·
      refine ⟨13608456775003769488676215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72578436133353437272939813 13608456775003769488676215)
      ·
        refine ⟨20412685162505654233014323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13608456775003769488676215 20412685162505654233014323)
        ·
          refine ⟨30619027743758481349521485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20412685162505654233014323 30619027743758481349521485)
          ·
            refine ⟨11482135403909430506070557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30619027743758481349521485 11482135403909430506070557)
            ·
              refine ⟨4305800776466036439776459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11482135403909430506070557 4305800776466036439776459)
              ·
                refine ⟨6458701164699054659664689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4305800776466036439776459 6458701164699054659664689)
                ·
                  refine ⟨4844025873524290994748517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6458701164699054659664689 4844025873524290994748517)
                  ·
                    refine ⟨908254851285804561515347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4844025873524290994748517 908254851285804561515347)
                    ·
                      rfl

theorem cell23_5306460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_5306460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306460 prefixEnd_5306460 := by exact prefixLift 5306460
  have htrace : WordTrace (prefixWord ++ tailWord_5306460) baseStart_5306460 baseEnd_5306460 := by
    simpa [prefixWord, tailWord_5306460, baseEnd_5306460] using wordTrace_append hprefix tailTrace_5306460
  have hstable : (prefixWord ++ tailWord_5306460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306460).length < 2 ^ (prefixWord ++ tailWord_5306460).sum := by decide
  have hdescent : baseEnd_5306460 < baseStart_5306460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306479 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 5]
def baseStart_5306479 : Nat := 118140960795 + 5306479 * 2 ^ 59
def prefixEnd_5306479 : Nat := 4983230072969 + 3 ^ 40 * 5306479 * 2
def baseEnd_5306479 : Nat := 2724774309989849110208453

theorem tailTrace_5306479 : CollatzResearch.WordTrace tailWord_5306479 prefixEnd_5306479 2724774309989849110208453 := by
  unfold tailWord_5306479
  simp only [CollatzResearch.WordTrace]
  refine ⟨193543189342540332306114491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129028792895026888204076327 193543189342540332306114491)
  ·
    refine ⟨290314784013810498459171737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193543189342540332306114491 290314784013810498459171737)
    ·
      refine ⟨217736088010357873844378803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290314784013810498459171737 217736088010357873844378803)
      ·
        refine ⟨326604132015536810766568205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217736088010357873844378803 326604132015536810766568205)
        ·
          refine ⟨122476549505826304037463077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326604132015536810766568205 122476549505826304037463077)
          ·
            refine ⟨22964353032342432007024327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122476549505826304037463077 22964353032342432007024327)
            ·
              refine ⟨34446529548513648010536491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22964353032342432007024327 34446529548513648010536491)
              ·
                refine ⟨51669794322770472015804737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34446529548513648010536491 51669794322770472015804737)
                ·
                  refine ⟨38752345742077854011853553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51669794322770472015804737 38752345742077854011853553)
                  ·
                    refine ⟨29064259306558390508890165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38752345742077854011853553 29064259306558390508890165)
                    ·
                      refine ⟨2724774309989849110208453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29064259306558390508890165 2724774309989849110208453)
                      ·
                        rfl

theorem cell23_5306479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_5306479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306479 prefixEnd_5306479 := by exact prefixLift 5306479
  have htrace : WordTrace (prefixWord ++ tailWord_5306479) baseStart_5306479 baseEnd_5306479 := by
    simpa [prefixWord, tailWord_5306479, baseEnd_5306479] using wordTrace_append hprefix tailTrace_5306479
  have hstable : (prefixWord ++ tailWord_5306479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306479).length < 2 ^ (prefixWord ++ tailWord_5306479).sum := by decide
  have hdescent : baseEnd_5306479 < baseStart_5306479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306518 : List Nat := [5, 3, 2, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_5306518 : Nat := 118140960795 + 5306518 * 2 ^ 59
def prefixEnd_5306518 : Nat := 4983230072969 + 3 ^ 40 * 5306518 * 2
def baseEnd_5306518 : Nat := 2724794335735374457620775

theorem tailTrace_5306518 : CollatzResearch.WordTrace tailWord_5306518 prefixEnd_5306518 2724794335735374457620775 := by
  unfold tailWord_5306518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12096538236837440122924013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129029741192932694644522805 12096538236837440122924013)
  ·
    refine ⟨4536201838814040046096505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12096538236837440122924013 4536201838814040046096505)
    ·
      refine ⟨3402151379110530034572379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4536201838814040046096505 3402151379110530034572379)
      ·
        refine ⟨5103227068665795051858569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3402151379110530034572379 5103227068665795051858569)
        ·
          refine ⟨3827420301499346288893927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5103227068665795051858569 3827420301499346288893927)
          ·
            refine ⟨5741130452249019433340891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3827420301499346288893927 5741130452249019433340891)
            ·
              refine ⟨8611695678373529150011337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5741130452249019433340891 8611695678373529150011337)
              ·
                refine ⟨6458771758780146862508503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8611695678373529150011337 6458771758780146862508503)
                ·
                  refine ⟨9688157638170220293762755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6458771758780146862508503 9688157638170220293762755)
                  ·
                    refine ⟨14532236457255330440644133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9688157638170220293762755 14532236457255330440644133)
                    ·
                      refine ⟨2724794335735374457620775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14532236457255330440644133 2724794335735374457620775)
                      ·
                        rfl

theorem cell23_5306518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_5306518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306518 prefixEnd_5306518 := by exact prefixLift 5306518
  have htrace : WordTrace (prefixWord ++ tailWord_5306518) baseStart_5306518 baseEnd_5306518 := by
    simpa [prefixWord, tailWord_5306518, baseEnd_5306518] using wordTrace_append hprefix tailTrace_5306518
  have hstable : (prefixWord ++ tailWord_5306518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306518).length < 2 ^ (prefixWord ++ tailWord_5306518).sum := by decide
  have hdescent : baseEnd_5306518 < baseStart_5306518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306527 : List Nat := [1, 1, 2, 6, 1, 3, 1, 2, 1, 3, 2]
def baseStart_5306527 : Nat := 118140960795 + 5306527 * 2 ^ 59
def prefixEnd_5306527 : Nat := 4983230072969 + 3 ^ 40 * 5306527 * 2
def baseEnd_5306527 : Nat := 2724798957061264922408233

theorem tailTrace_5306527 : CollatzResearch.WordTrace tailWord_5306527 prefixEnd_5306527 2724798957061264922408233 := by
  unfold tailWord_5306527
  simp only [CollatzResearch.WordTrace]
  refine ⟨193544940046366436503861835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129029960030910957669241223 193544940046366436503861835)
  ·
    refine ⟨290317410069549654755792753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193544940046366436503861835 290317410069549654755792753)
    ·
      refine ⟨217738057552162241066844565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290317410069549654755792753 217738057552162241066844565)
      ·
        refine ⟨10206471447757605050008339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 217738057552162241066844565 10206471447757605050008339)
        ·
          refine ⟨15309707171636407575012509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10206471447757605050008339 15309707171636407575012509)
          ·
            refine ⟨5741140189363652840629691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15309707171636407575012509 5741140189363652840629691)
            ·
              refine ⟨8611710284045479260944537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5741140189363652840629691 8611710284045479260944537)
              ·
                refine ⟨6458782713034109445708403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8611710284045479260944537 6458782713034109445708403)
                ·
                  refine ⟨9688174069551164168562605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6458782713034109445708403 9688174069551164168562605)
                  ·
                    refine ⟨3633065276081686563210977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9688174069551164168562605 3633065276081686563210977)
                    ·
                      refine ⟨2724798957061264922408233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3633065276081686563210977 2724798957061264922408233)
                      ·
                        rfl

theorem cell23_5306527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_5306527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306527 prefixEnd_5306527 := by exact prefixLift 5306527
  have htrace : WordTrace (prefixWord ++ tailWord_5306527) baseStart_5306527 baseEnd_5306527 := by
    simpa [prefixWord, tailWord_5306527, baseEnd_5306527] using wordTrace_append hprefix tailTrace_5306527
  have hstable : (prefixWord ++ tailWord_5306527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306527).length < 2 ^ (prefixWord ++ tailWord_5306527).sum := by decide
  have hdescent : baseEnd_5306527 < baseStart_5306527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306559 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 3, 7]
def baseStart_5306559 : Nat := 118140960795 + 5306559 * 2 ^ 59
def prefixEnd_5306559 : Nat := 4983230072969 + 3 ^ 40 * 5306559 * 2
def baseEnd_5306559 : Nat := 908271796147402932402695

theorem tailTrace_5306559 : CollatzResearch.WordTrace tailWord_5306559 prefixEnd_5306559 908271796147402932402695 := by
  unfold tailWord_5306559
  simp only [CollatzResearch.WordTrace]
  refine ⟨193546107182250505969026731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129030738121500337312684487 193546107182250505969026731)
  ·
    refine ⟨290319160773375758953540097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193546107182250505969026731 290319160773375758953540097)
    ·
      refine ⟨217739370580031819215155073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290319160773375758953540097 217739370580031819215155073)
      ·
        refine ⟨163304527935023864411366305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217739370580031819215155073 163304527935023864411366305)
        ·
          refine ⟨122478395951267898308524729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163304527935023864411366305 122478395951267898308524729)
          ·
            refine ⟨91858796963450923731393547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122478395951267898308524729 91858796963450923731393547)
            ·
              refine ⟨137788195445176385597090321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91858796963450923731393547 137788195445176385597090321)
              ·
                refine ⟨103341146583882289197817741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137788195445176385597090321 103341146583882289197817741)
                ·
                  refine ⟨38752929968955858449181653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103341146583882289197817741 38752929968955858449181653)
                  ·
                    refine ⟨908271796147402932402695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38752929968955858449181653 908271796147402932402695)
                    ·
                      rfl

theorem cell23_5306559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 7].length) (baseStart_5306559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306559 prefixEnd_5306559 := by exact prefixLift 5306559
  have htrace : WordTrace (prefixWord ++ tailWord_5306559) baseStart_5306559 baseEnd_5306559 := by
    simpa [prefixWord, tailWord_5306559, baseEnd_5306559] using wordTrace_append hprefix tailTrace_5306559
  have hstable : (prefixWord ++ tailWord_5306559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306559).length < 2 ^ (prefixWord ++ tailWord_5306559).sum := by decide
  have hdescent : baseEnd_5306559 < baseStart_5306559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306569 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 7]
def baseStart_5306569 : Nat := 118140960795 + 5306569 * 2 ^ 59
def prefixEnd_5306569 : Nat := 4983230072969 + 3 ^ 40 * 5306569 * 2
def baseEnd_5306569 : Nat := 2724820523248753758083039

theorem tailTrace_5306569 : CollatzResearch.WordTrace tailWord_5306569 prefixEnd_5306569 2724820523248753758083039 := by
  unfold tailWord_5306569
  simp only [CollatzResearch.WordTrace]
  refine ⟨193546471912214277676890761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129030981274809518451260507 193546471912214277676890761)
  ·
    refine ⟨145159853934160708257668071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193546471912214277676890761 145159853934160708257668071)
    ·
      refine ⟨217739780901241062386502107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145159853934160708257668071 217739780901241062386502107)
      ·
        refine ⟨326609671351861593579753161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217739780901241062386502107 326609671351861593579753161)
        ·
          refine ⟨244957253513896195184814871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326609671351861593579753161 244957253513896195184814871)
          ·
            refine ⟨367435880270844292777222307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244957253513896195184814871 367435880270844292777222307)
            ·
              refine ⟨551153820406266439165833461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367435880270844292777222307 551153820406266439165833461)
              ·
                refine ⟨51670670663087478671796887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 551153820406266439165833461 51670670663087478671796887)
                ·
                  refine ⟨77506005994631218007695331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51670670663087478671796887 77506005994631218007695331)
                  ·
                    refine ⟨116259008991946827011542997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77506005994631218007695331 116259008991946827011542997)
                    ·
                      refine ⟨2724820523248753758083039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116259008991946827011542997 2724820523248753758083039)
                      ·
                        rfl

theorem cell23_5306569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_5306569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306569 prefixEnd_5306569 := by exact prefixLift 5306569
  have htrace : WordTrace (prefixWord ++ tailWord_5306569) baseStart_5306569 baseEnd_5306569 := by
    simpa [prefixWord, tailWord_5306569, baseEnd_5306569] using wordTrace_append hprefix tailTrace_5306569
  have hstable : (prefixWord ++ tailWord_5306569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306569).length < 2 ^ (prefixWord ++ tailWord_5306569).sum := by decide
  have hdescent : baseEnd_5306569 < baseStart_5306569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306623 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 3, 4]
def baseStart_5306623 : Nat := 118140960795 + 5306623 * 2 ^ 59
def prefixEnd_5306623 : Nat := 4983230072969 + 3 ^ 40 * 5306623 * 2
def baseEnd_5306623 : Nat := 908282750401365515602597

theorem tailTrace_5306623 : CollatzResearch.WordTrace tailWord_5306623 prefixEnd_5306623 908282750401365515602597 := by
  unfold tailWord_5306623
  simp only [CollatzResearch.WordTrace]
  refine ⟨193548441454018644899356523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129032294302679096599571015 193548441454018644899356523)
  ·
    refine ⟨290322662181027967349034785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193548441454018644899356523 290322662181027967349034785)
    ·
      refine ⟨217741996635770975511776089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290322662181027967349034785 217741996635770975511776089)
      ·
        refine ⟨163306497476828231633832067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217741996635770975511776089 163306497476828231633832067)
        ·
          refine ⟨244959746215242347450748101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163306497476828231633832067 244959746215242347450748101)
          ·
            refine ⟨45929952415357940147015269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 244959746215242347450748101 45929952415357940147015269)
            ·
              refine ⟨8611866077879613777565363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45929952415357940147015269 8611866077879613777565363)
              ·
                refine ⟨12917799116819420666348045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8611866077879613777565363 12917799116819420666348045)
                ·
                  refine ⟨4844174668807282749880517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12917799116819420666348045 4844174668807282749880517)
                  ·
                    refine ⟨908282750401365515602597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4844174668807282749880517 908282750401365515602597)
                    ·
                      rfl

theorem cell23_5306623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 4].length) (baseStart_5306623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306623 prefixEnd_5306623 := by exact prefixLift 5306623
  have htrace : WordTrace (prefixWord ++ tailWord_5306623) baseStart_5306623 baseEnd_5306623 := by
    simpa [prefixWord, tailWord_5306623, baseEnd_5306623] using wordTrace_append hprefix tailTrace_5306623
  have hstable : (prefixWord ++ tailWord_5306623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306623).length < 2 ^ (prefixWord ++ tailWord_5306623).sum := by decide
  have hdescent : baseEnd_5306623 < baseStart_5306623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306674 : List Nat := [3, 2, 1, 1, 5, 1, 3, 2, 1, 4]
def baseStart_5306674 : Nat := 118140960795 + 5306674 * 2 ^ 59
def prefixEnd_5306674 : Nat := 4983230072969 + 3 ^ 40 * 5306674 * 2
def baseEnd_5306674 : Nat := 908291479572491949090019

theorem tailTrace_5306674 : CollatzResearch.WordTrace tailWord_5306674 prefixEnd_5306674 908291479572491949090019 := by
  unfold tailWord_5306674
  simp only [CollatzResearch.WordTrace]
  refine ⟨48387575394208470152365769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129033534384555920406308717 48387575394208470152365769)
  ·
    refine ⟨36290681545656352614274327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48387575394208470152365769 36290681545656352614274327)
    ·
      refine ⟨54436022318484528921411491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36290681545656352614274327 54436022318484528921411491)
      ·
        refine ⟨81654033477726793382117237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54436022318484528921411491 81654033477726793382117237)
        ·
          refine ⟨7655065638536886879573491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81654033477726793382117237 7655065638536886879573491)
          ·
            refine ⟨11482598457805330319360237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7655065638536886879573491 11482598457805330319360237)
            ·
              refine ⟨4305974421676998869760089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11482598457805330319360237 4305974421676998869760089)
              ·
                refine ⟨3229480816257749152320067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4305974421676998869760089 3229480816257749152320067)
                ·
                  refine ⟨4844221224386623728480101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3229480816257749152320067 4844221224386623728480101)
                  ·
                    refine ⟨908291479572491949090019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4844221224386623728480101 908291479572491949090019)
                    ·
                      rfl

theorem cell23_5306674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_5306674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306674 prefixEnd_5306674 := by exact prefixLift 5306674
  have htrace : WordTrace (prefixWord ++ tailWord_5306674) baseStart_5306674 baseEnd_5306674 := by
    simpa [prefixWord, tailWord_5306674, baseEnd_5306674] using wordTrace_append hprefix tailTrace_5306674
  have hstable : (prefixWord ++ tailWord_5306674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306674).length < 2 ^ (prefixWord ++ tailWord_5306674).sum := by decide
  have hdescent : baseEnd_5306674 < baseStart_5306674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306680 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 3, 1, 3]
def baseStart_5306680 : Nat := 118140960795 + 5306680 * 2 ^ 59
def prefixEnd_5306680 : Nat := 4983230072969 + 3 ^ 40 * 5306680 * 2
def baseEnd_5306680 : Nat := 2724877519601402823795029

theorem tailTrace_5306680 : CollatzResearch.WordTrace tailWord_5306680 prefixEnd_5306680 2724877519601402823795029 := by
  unfold tailWord_5306680
  simp only [CollatzResearch.WordTrace]
  refine ⟨96775260207406071817090747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129033680276541429089454329 96775260207406071817090747)
  ·
    refine ⟨145162890311109107725636121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96775260207406071817090747 145162890311109107725636121)
    ·
      refine ⟨108872167733331830794227091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145162890311109107725636121 108872167733331830794227091)
      ·
        refine ⟨163308251599997746191340637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108872167733331830794227091 163308251599997746191340637)
        ·
          refine ⟨61240594349999154821752739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163308251599997746191340637 61240594349999154821752739)
          ·
            refine ⟨91860891524998732232629109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61240594349999154821752739 91860891524998732232629109)
            ·
              refine ⟨8611958580468631146808979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91860891524998732232629109 8611958580468631146808979)
              ·
                refine ⟨12917937870702946720213469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8611958580468631146808979 12917937870702946720213469)
                ·
                  refine ⟨4844226701513605020080051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12917937870702946720213469 4844226701513605020080051)
                  ·
                    refine ⟨7266340052270407530120077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4844226701513605020080051 7266340052270407530120077)
                    ·
                      refine ⟨2724877519601402823795029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7266340052270407530120077 2724877519601402823795029)
                      ·
                        rfl

theorem cell23_5306680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 3, 1, 3].length) (baseStart_5306680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306680 prefixEnd_5306680 := by exact prefixLift 5306680
  have htrace : WordTrace (prefixWord ++ tailWord_5306680) baseStart_5306680 baseEnd_5306680 := by
    simpa [prefixWord, tailWord_5306680, baseEnd_5306680] using wordTrace_append hprefix tailTrace_5306680
  have hstable : (prefixWord ++ tailWord_5306680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306680).length < 2 ^ (prefixWord ++ tailWord_5306680).sum := by decide
  have hdescent : baseEnd_5306680 < baseStart_5306680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306703 : List Nat := [1, 1, 2, 1, 1, 2, 1, 8, 1, 1, 4]
def baseStart_5306703 : Nat := 118140960795 + 5306703 * 2 ^ 59
def prefixEnd_5306703 : Nat := 4983230072969 + 3 ^ 40 * 5306703 * 2
def baseEnd_5306703 : Nat := 2724889329656456233807423

theorem tailTrace_5306703 : CollatzResearch.WordTrace tailWord_5306703 prefixEnd_5306703 2724889329656456233807423 := by
  unfold tailWord_5306703
  simp only [CollatzResearch.WordTrace]
  refine ⟨193551359293728818562268763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129034239529152545708179175 193551359293728818562268763)
  ·
    refine ⟨290327038940593227843403145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193551359293728818562268763 290327038940593227843403145)
    ·
      refine ⟨217745279205444920882552359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290327038940593227843403145 217745279205444920882552359)
      ·
        refine ⟨326617918808167381323828539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217745279205444920882552359 326617918808167381323828539)
        ·
          refine ⟨489926878212251071985742809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326617918808167381323828539 489926878212251071985742809)
          ·
            refine ⟨367445158659188303989307107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489926878212251071985742809 367445158659188303989307107)
            ·
              refine ⟨551167737988782455983960661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367445158659188303989307107 551167737988782455983960661)
              ·
                refine ⟨6458996929556044406062039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 551167737988782455983960661 6458996929556044406062039)
                ·
                  refine ⟨9688495394334066609093059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6458996929556044406062039 9688495394334066609093059)
                  ·
                    refine ⟨14532743091501099913639589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9688495394334066609093059 14532743091501099913639589)
                    ·
                      refine ⟨2724889329656456233807423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14532743091501099913639589 2724889329656456233807423)
                      ·
                        rfl

theorem cell23_5306703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 1, 4].length) (baseStart_5306703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306703 prefixEnd_5306703 := by exact prefixLift 5306703
  have htrace : WordTrace (prefixWord ++ tailWord_5306703) baseStart_5306703 baseEnd_5306703 := by
    simpa [prefixWord, tailWord_5306703, baseEnd_5306703] using wordTrace_append hprefix tailTrace_5306703
  have hstable : (prefixWord ++ tailWord_5306703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306703).length < 2 ^ (prefixWord ++ tailWord_5306703).sum := by decide
  have hdescent : baseEnd_5306703 < baseStart_5306703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306733 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_5306733 : Nat := 118140960795 + 5306733 * 2 ^ 59
def prefixEnd_5306733 : Nat := 4983230072969 + 3 ^ 40 * 5306733 * 2
def baseEnd_5306733 : Nat := 2724904734076091116432285

theorem tailTrace_5306733 : CollatzResearch.WordTrace tailWord_5306733 prefixEnd_5306733 2724904734076091116432285 := by
  unfold tailWord_5306733
  simp only [CollatzResearch.WordTrace]
  refine ⟨193552453483620133685860853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129034968989080089123907235 193552453483620133685860853)
  ·
    refine ⟨18145542514089387533049455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193552453483620133685860853 18145542514089387533049455)
    ·
      refine ⟨27218313771134081299574183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18145542514089387533049455 27218313771134081299574183)
      ·
        refine ⟨40827470656701121949361275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27218313771134081299574183 40827470656701121949361275)
        ·
          refine ⟨61241205985051682924041913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40827470656701121949361275 61241205985051682924041913)
          ·
            refine ⟨45930904488788762193031435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61241205985051682924041913 45930904488788762193031435)
            ·
              refine ⟨68896356733183143289547153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45930904488788762193031435 68896356733183143289547153)
              ·
                refine ⟨51672267549887357467160365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68896356733183143289547153 51672267549887357467160365)
                ·
                  refine ⟨19377100331207759050185137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51672267549887357467160365 19377100331207759050185137)
                  ·
                    refine ⟨14532825248405819287638853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19377100331207759050185137 14532825248405819287638853)
                    ·
                      refine ⟨2724904734076091116432285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14532825248405819287638853 2724904734076091116432285)
                      ·
                        rfl

theorem cell23_5306733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_5306733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306733 prefixEnd_5306733 := by exact prefixLift 5306733
  have htrace : WordTrace (prefixWord ++ tailWord_5306733) baseStart_5306733 baseEnd_5306733 := by
    simpa [prefixWord, tailWord_5306733, baseEnd_5306733] using wordTrace_append hprefix tailTrace_5306733
  have hstable : (prefixWord ++ tailWord_5306733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306733).length < 2 ^ (prefixWord ++ tailWord_5306733).sum := by decide
  have hdescent : baseEnd_5306733 < baseStart_5306733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306787 : List Nat := [1, 1, 1, 4, 1, 4, 3, 2, 2, 1, 3]
def baseStart_5306787 : Nat := 118140960795 + 5306787 * 2 ^ 59
def prefixEnd_5306787 : Nat := 4983230072969 + 3 ^ 40 * 5306787 * 2
def baseEnd_5306787 : Nat := 2724932462031433905157037

theorem tailTrace_5306787 : CollatzResearch.WordTrace tailWord_5306787 prefixEnd_5306787 2724932462031433905157037 := by
  unfold tailWord_5306787
  simp only [CollatzResearch.WordTrace]
  refine ⟨193554423025424500908326615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129036282016949667272217743 193554423025424500908326615)
  ·
    refine ⟨290331634538136751362489923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193554423025424500908326615 290331634538136751362489923)
    ·
      refine ⟨435497451807205127043734885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290331634538136751362489923 435497451807205127043734885)
      ·
        refine ⟨81655772213850961320700291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 435497451807205127043734885 81655772213850961320700291)
        ·
          refine ⟨122483658320776441981050437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81655772213850961320700291 122483658320776441981050437)
          ·
            refine ⟨22965685935145582871446957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122483658320776441981050437 22965685935145582871446957)
            ·
              refine ⟨8612132225679593576792609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22965685935145582871446957 8612132225679593576792609)
              ·
                refine ⟨6459099169259695182594457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8612132225679593576792609 6459099169259695182594457)
                ·
                  refine ⟨4844324376944771386945843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6459099169259695182594457 4844324376944771386945843)
                  ·
                    refine ⟨7266486565417157080418765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4844324376944771386945843 7266486565417157080418765)
                    ·
                      refine ⟨2724932462031433905157037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7266486565417157080418765 2724932462031433905157037)
                      ·
                        rfl

theorem cell23_5306787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_5306787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306787 prefixEnd_5306787 := by exact prefixLift 5306787
  have htrace : WordTrace (prefixWord ++ tailWord_5306787) baseStart_5306787 baseEnd_5306787 := by
    simpa [prefixWord, tailWord_5306787, baseEnd_5306787] using wordTrace_append hprefix tailTrace_5306787
  have hstable : (prefixWord ++ tailWord_5306787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306787).length < 2 ^ (prefixWord ++ tailWord_5306787).sum := by decide
  have hdescent : baseEnd_5306787 < baseStart_5306787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306861 : List Nat := [1, 5, 1, 3, 1, 2, 1, 3, 2, 2, 2]
def baseStart_5306861 : Nat := 118140960795 + 5306861 * 2 ^ 59
def prefixEnd_5306861 : Nat := 4983230072969 + 3 ^ 40 * 5306861 * 2
def baseEnd_5306861 : Nat := 2724970459599866615631697

theorem tailTrace_5306861 : CollatzResearch.WordTrace tailWord_5306861 prefixEnd_5306861 2724970459599866615631697 := by
  unfold tailWord_5306861
  simp only [CollatzResearch.WordTrace]
  refine ⟨193557122027156411546520437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129038081351437607697680291 193557122027156411546520437)
  ·
    refine ⟨18145980190045913582486291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193557122027156411546520437 18145980190045913582486291)
    ·
      refine ⟨27218970285068870373729437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18145980190045913582486291 27218970285068870373729437)
      ·
        refine ⟨10207113856900826390148539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27218970285068870373729437 10207113856900826390148539)
        ·
          refine ⟨15310670785351239585222809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10207113856900826390148539 15310670785351239585222809)
          ·
            refine ⟨11483003089013429688917107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15310670785351239585222809 11483003089013429688917107)
            ·
              refine ⟨17224504633520144533375661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11483003089013429688917107 17224504633520144533375661)
              ·
                refine ⟨6459189237570054200015873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17224504633520144533375661 6459189237570054200015873)
                ·
                  refine ⟨4844391928177540650011905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6459189237570054200015873 4844391928177540650011905)
                  ·
                    refine ⟨3633293946133155487508929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4844391928177540650011905 3633293946133155487508929)
                    ·
                      refine ⟨2724970459599866615631697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3633293946133155487508929 2724970459599866615631697)
                      ·
                        rfl

theorem cell23_5306861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_5306861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306861 prefixEnd_5306861 := by exact prefixLift 5306861
  have htrace : WordTrace (prefixWord ++ tailWord_5306861) baseStart_5306861 baseEnd_5306861 := by
    simpa [prefixWord, tailWord_5306861, baseEnd_5306861] using wordTrace_append hprefix tailTrace_5306861
  have hstable : (prefixWord ++ tailWord_5306861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306861).length < 2 ^ (prefixWord ++ tailWord_5306861).sum := by decide
  have hdescent : baseEnd_5306861 < baseStart_5306861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306863 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 6, 5]
def baseStart_5306863 : Nat := 118140960795 + 5306863 * 2 ^ 59
def prefixEnd_5306863 : Nat := 4983230072969 + 3 ^ 40 * 5306863 * 2
def baseEnd_5306863 : Nat := 908323828853725202602229

theorem tailTrace_5306863 : CollatzResearch.WordTrace tailWord_5306863 prefixEnd_5306863 908323828853725202602229 := by
  unfold tailWord_5306863
  simp only [CollatzResearch.WordTrace]
  refine ⟨193557194973149165888093243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129038129982099443925395495 193557194973149165888093243)
  ·
    refine ⟨290335792459723748832139865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193557194973149165888093243 290335792459723748832139865)
    ·
      refine ⟨217751844344792811624104899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290335792459723748832139865 217751844344792811624104899)
      ·
        refine ⟨326627766517189217436157349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217751844344792811624104899 326627766517189217436157349)
        ·
          refine ⟨61242706221972978269279503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 326627766517189217436157349 61242706221972978269279503)
          ·
            refine ⟨91864059332959467403919255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61242706221972978269279503 91864059332959467403919255)
            ·
              refine ⟨137796088999439201105878883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91864059332959467403919255 137796088999439201105878883)
              ·
                refine ⟨206694133499158801658818325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137796088999439201105878883 206694133499158801658818325)
                ·
                  refine ⟨9688787507773068827757109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 206694133499158801658818325 9688787507773068827757109)
                  ·
                    refine ⟨908323828853725202602229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9688787507773068827757109 908323828853725202602229)
                    ·
                      rfl

theorem cell23_5306863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 5].length) (baseStart_5306863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306863 prefixEnd_5306863 := by exact prefixLift 5306863
  have htrace : WordTrace (prefixWord ++ tailWord_5306863) baseStart_5306863 baseEnd_5306863 := by
    simpa [prefixWord, tailWord_5306863, baseEnd_5306863] using wordTrace_append hprefix tailTrace_5306863
  have hstable : (prefixWord ++ tailWord_5306863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306863).length < 2 ^ (prefixWord ++ tailWord_5306863).sum := by decide
  have hdescent : baseEnd_5306863 < baseStart_5306863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306934 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_5306934 : Nat := 118140960795 + 5306934 * 2 ^ 59
def prefixEnd_5306934 : Nat := 4983230072969 + 3 ^ 40 * 5306934 * 2
def baseEnd_5306934 : Nat := 2725007943687644830018861

theorem tailTrace_5306934 : CollatzResearch.WordTrace tailWord_5306934 prefixEnd_5306934 2725007943687644830018861 := by
  unfold tailWord_5306934
  simp only [CollatzResearch.WordTrace]
  refine ⟨12097486534743246563370491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129039856370594630009285237 12097486534743246563370491)
  ·
    refine ⟨18146229802114869845055737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12097486534743246563370491 18146229802114869845055737)
    ·
      refine ⟨13609672351586152383791803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18146229802114869845055737 13609672351586152383791803)
      ·
        refine ⟨20414508527379228575687705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13609672351586152383791803 20414508527379228575687705)
        ·
          refine ⟨15310881395534421431765779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20414508527379228575687705 15310881395534421431765779)
          ·
            refine ⟨22966322093301632147648669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15310881395534421431765779 22966322093301632147648669)
            ·
              refine ⟨8612370784988112055368251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22966322093301632147648669 8612370784988112055368251)
              ·
                refine ⟨12918556177482168083052377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8612370784988112055368251 12918556177482168083052377)
                ·
                  refine ⟨9688917133111626062289283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12918556177482168083052377 9688917133111626062289283)
                  ·
                    refine ⟨14533375699667439093433925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9688917133111626062289283 14533375699667439093433925)
                    ·
                      refine ⟨2725007943687644830018861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14533375699667439093433925 2725007943687644830018861)
                      ·
                        rfl

theorem cell23_5306934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_5306934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306934 prefixEnd_5306934 := by exact prefixLift 5306934
  have htrace : WordTrace (prefixWord ++ tailWord_5306934) baseStart_5306934 baseEnd_5306934 := by
    simpa [prefixWord, tailWord_5306934, baseEnd_5306934] using wordTrace_append hprefix tailTrace_5306934
  have hstable : (prefixWord ++ tailWord_5306934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306934).length < 2 ^ (prefixWord ++ tailWord_5306934).sum := by decide
  have hdescent : baseEnd_5306934 < baseStart_5306934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306957 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 8]
def baseStart_5306957 : Nat := 118140960795 + 5306957 * 2 ^ 59
def prefixEnd_5306957 : Nat := 4983230072969 + 3 ^ 40 * 5306957 * 2
def baseEnd_5306957 : Nat := 302779972638077582225695

theorem tailTrace_5306957 : CollatzResearch.WordTrace tailWord_5306957 prefixEnd_5306957 302779972638077582225695 := by
  unfold tailWord_5306957
  simp only [CollatzResearch.WordTrace]
  refine ⟨193560623434808619942015125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129040415623205746628010083 193560623434808619942015125)
  ·
    refine ⟨9073154223506654059781959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 193560623434808619942015125 9073154223506654059781959)
    ·
      refine ⟨13609731335259981089672939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9073154223506654059781959 13609731335259981089672939)
      ·
        refine ⟨20414597002889971634509409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13609731335259981089672939 20414597002889971634509409)
        ·
          refine ⟨15310947752167478725882057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20414597002889971634509409 15310947752167478725882057)
          ·
            refine ⟨11483210814125609044411543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15310947752167478725882057 11483210814125609044411543)
            ·
              refine ⟨17224816221188413566617315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11483210814125609044411543 17224816221188413566617315)
              ·
                refine ⟨25837224331782620349925973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17224816221188413566617315 25837224331782620349925973)
                ·
                  refine ⟨302779972638077582225695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25837224331782620349925973 302779972638077582225695)
                  ·
                    rfl

theorem cell23_5306957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_5306957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306957 prefixEnd_5306957 := by exact prefixLift 5306957
  have htrace : WordTrace (prefixWord ++ tailWord_5306957) baseStart_5306957 baseEnd_5306957 := by
    simpa [prefixWord, tailWord_5306957, baseEnd_5306957] using wordTrace_append hprefix tailTrace_5306957
  have hstable : (prefixWord ++ tailWord_5306957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306957).length < 2 ^ (prefixWord ++ tailWord_5306957).sum := by decide
  have hdescent : baseEnd_5306957 < baseStart_5306957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5306977 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 1, 5, 2]
def baseStart_5306977 : Nat := 118140960795 + 5306977 * 2 ^ 59
def prefixEnd_5306977 : Nat := 4983230072969 + 3 ^ 40 * 5306977 * 2
def baseEnd_5306977 : Nat := 2725030023355788161781163

theorem tailTrace_5306977 : CollatzResearch.WordTrace tailWord_5306977 prefixEnd_5306977 2725030023355788161781163 := by
  unfold tailWord_5306977
  simp only [CollatzResearch.WordTrace]
  refine ⟨193561352894736163357743185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129040901929824108905162123 193561352894736163357743185)
  ·
    refine ⟨145171014671052122518307389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193561352894736163357743185 145171014671052122518307389)
    ·
      refine ⟨54439130501644545944365271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145171014671052122518307389 54439130501644545944365271)
      ·
        refine ⟨81658695752466818916547907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54439130501644545944365271 81658695752466818916547907)
        ·
          refine ⟨122488043628700228374821861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81658695752466818916547907 122488043628700228374821861)
          ·
            refine ⟨22966508180381292820279099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122488043628700228374821861 22966508180381292820279099)
            ·
              refine ⟨34449762270571939230418649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22966508180381292820279099 34449762270571939230418649)
              ·
                refine ⟨25837321702928954422813987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34449762270571939230418649 25837321702928954422813987)
                ·
                  refine ⟨38755982554393431634220981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25837321702928954422813987 38755982554393431634220981)
                  ·
                    refine ⟨3633373364474384215708217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38755982554393431634220981 3633373364474384215708217)
                    ·
                      refine ⟨2725030023355788161781163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3633373364474384215708217 2725030023355788161781163)
                      ·
                        rfl

theorem cell23_5306977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_5306977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5306977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5306977 prefixEnd_5306977 := by exact prefixLift 5306977
  have htrace : WordTrace (prefixWord ++ tailWord_5306977) baseStart_5306977 baseEnd_5306977 := by
    simpa [prefixWord, tailWord_5306977, baseEnd_5306977] using wordTrace_append hprefix tailTrace_5306977
  have hstable : (prefixWord ++ tailWord_5306977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5306977).length < 2 ^ (prefixWord ++ tailWord_5306977).sum := by decide
  have hdescent : baseEnd_5306977 < baseStart_5306977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5306977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307001 : List Nat := [1, 2, 1, 3, 3, 2, 3, 3, 1, 1, 3]
def baseStart_5307001 : Nat := 118140960795 + 5307001 * 2 ^ 59
def prefixEnd_5307001 : Nat := 4983230072969 + 3 ^ 40 * 5307001 * 2
def baseEnd_5307001 : Nat := 2725042346891496067881053

theorem tailTrace_5307001 : CollatzResearch.WordTrace tailWord_5307001 prefixEnd_5307001 2725042346891496067881053 := by
  unfold tailWord_5307001
  simp only [CollatzResearch.WordTrace]
  refine ⟨193562228246649215456616857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129041485497766143637744571 193562228246649215456616857)
  ·
    refine ⟨145171671184986911592462643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193562228246649215456616857 145171671184986911592462643)
    ·
      refine ⟨217757506777480367388693965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145171671184986911592462643 217757506777480367388693965)
      ·
        refine ⟨81659065041555137770760237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217757506777480367388693965 81659065041555137770760237)
        ·
          refine ⟨30622149390583176664035089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81659065041555137770760237 30622149390583176664035089)
          ·
            refine ⟨22966612042937382498026317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30622149390583176664035089 22966612042937382498026317)
            ·
              refine ⟨8612479516101518436759869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22966612042937382498026317 8612479516101518436759869)
              ·
                refine ⟨3229679818538069413784951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8612479516101518436759869 3229679818538069413784951)
                ·
                  refine ⟨4844519727807104120677427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3229679818538069413784951 4844519727807104120677427)
                  ·
                    refine ⟨7266779591710656181016141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4844519727807104120677427 7266779591710656181016141)
                    ·
                      refine ⟨2725042346891496067881053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7266779591710656181016141 2725042346891496067881053)
                      ·
                        rfl

theorem cell23_5307001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_5307001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307001 prefixEnd_5307001 := by exact prefixLift 5307001
  have htrace : WordTrace (prefixWord ++ tailWord_5307001) baseStart_5307001 baseEnd_5307001 := by
    simpa [prefixWord, tailWord_5307001, baseEnd_5307001] using wordTrace_append hprefix tailTrace_5307001
  have hstable : (prefixWord ++ tailWord_5307001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307001).length < 2 ^ (prefixWord ++ tailWord_5307001).sum := by decide
  have hdescent : baseEnd_5307001 < baseStart_5307001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307017 : List Nat := [1, 2, 1, 1, 4, 1, 1, 6, 2, 4]
def baseStart_5307017 : Nat := 118140960795 + 5307017 * 2 ^ 59
def prefixEnd_5307017 : Nat := 4983230072969 + 3 ^ 40 * 5307017 * 2
def baseEnd_5307017 : Nat := 908350187527322668426993

theorem tailTrace_5307017 : CollatzResearch.WordTrace tailWord_5307017 prefixEnd_5307017 908350187527322668426993 := by
  unfold tailWord_5307017
  simp only [CollatzResearch.WordTrace]
  refine ⟨193562811814591250189199305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129041874543060833459466203 193562811814591250189199305)
  ·
    refine ⟨145172108860943437641899479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193562811814591250189199305 145172108860943437641899479)
    ·
      refine ⟨217758163291415156462849219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145172108860943437641899479 217758163291415156462849219)
      ·
        refine ⟨326637244937122734694273829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217758163291415156462849219 326637244937122734694273829)
        ·
          refine ⟨61244483425710512755176343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 326637244937122734694273829 61244483425710512755176343)
          ·
            refine ⟨91866725138565769132764515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61244483425710512755176343 91866725138565769132764515)
            ·
              refine ⟨137800087707848653699146773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91866725138565769132764515 137800087707848653699146773)
              ·
                refine ⟨6459379111305405642147505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 137800087707848653699146773 6459379111305405642147505)
                ·
                  refine ⟨4844534333479054231610629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6459379111305405642147505 4844534333479054231610629)
                  ·
                    refine ⟨908350187527322668426993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4844534333479054231610629 908350187527322668426993)
                    ·
                      rfl

theorem cell23_5307017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 4].length) (baseStart_5307017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307017 prefixEnd_5307017 := by exact prefixLift 5307017
  have htrace : WordTrace (prefixWord ++ tailWord_5307017) baseStart_5307017 baseEnd_5307017 := by
    simpa [prefixWord, tailWord_5307017, baseEnd_5307017] using wordTrace_append hprefix tailTrace_5307017
  have hstable : (prefixWord ++ tailWord_5307017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307017).length < 2 ^ (prefixWord ++ tailWord_5307017).sum := by decide
  have hdescent : baseEnd_5307017 < baseStart_5307017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307018 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 3, 1, 3]
def baseStart_5307018 : Nat := 118140960795 + 5307018 * 2 ^ 59
def prefixEnd_5307018 : Nat := 4983230072969 + 3 ^ 40 * 5307018 * 2
def baseEnd_5307018 : Nat := 2725051076062622501368475

theorem tailTrace_5307018 : CollatzResearch.WordTrace tailWord_5307018 prefixEnd_5307018 2725051076062622501368475 := by
  unfold tailWord_5307018
  simp only [CollatzResearch.WordTrace]
  refine ⟨48390712071896906839996427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129041898858391751573323805 48390712071896906839996427)
  ·
    refine ⟨72586068107845360259994641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48390712071896906839996427 72586068107845360259994641)
    ·
      refine ⟨54439551080884020194995981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72586068107845360259994641 54439551080884020194995981)
      ·
        refine ⟨20414831655331507573123493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54439551080884020194995981 20414831655331507573123493)
        ·
          refine ⟨3827780935374657669960655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20414831655331507573123493 3827780935374657669960655)
          ·
            refine ⟨5741671403061986504940983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3827780935374657669960655 5741671403061986504940983)
            ·
              refine ⟨8612507104592979757411475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5741671403061986504940983 8612507104592979757411475)
              ·
                refine ⟨12918760656889469636117213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8612507104592979757411475 12918760656889469636117213)
                ·
                  refine ⟨4844535246333551113543955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12918760656889469636117213 4844535246333551113543955)
                  ·
                    refine ⟨7266802869500326670315933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4844535246333551113543955 7266802869500326670315933)
                    ·
                      refine ⟨2725051076062622501368475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7266802869500326670315933 2725051076062622501368475)
                      ·
                        rfl

theorem cell23_5307018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_5307018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307018 prefixEnd_5307018 := by exact prefixLift 5307018
  have htrace : WordTrace (prefixWord ++ tailWord_5307018) baseStart_5307018 baseEnd_5307018 := by
    simpa [prefixWord, tailWord_5307018, baseEnd_5307018] using wordTrace_append hprefix tailTrace_5307018
  have hstable : (prefixWord ++ tailWord_5307018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307018).length < 2 ^ (prefixWord ++ tailWord_5307018).sum := by decide
  have hdescent : baseEnd_5307018 < baseStart_5307018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307020 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 5, 2, 4]
def baseStart_5307020 : Nat := 118140960795 + 5307020 * 2 ^ 59
def prefixEnd_5307020 : Nat := 4983230072969 + 3 ^ 40 * 5307020 * 2
def baseEnd_5307020 : Nat := 2725052103023931493543465

theorem tailTrace_5307020 : CollatzResearch.WordTrace tailWord_5307020 prefixEnd_5307020 2725052103023931493543465 := by
  unfold tailWord_5307020
  simp only [CollatzResearch.WordTrace]
  refine ⟨96781460616790190850779257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129041947489053587801039009 96781460616790190850779257)
  ·
    refine ⟨72586095462592643138084443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96781460616790190850779257 72586095462592643138084443)
    ·
      refine ⟨108879143193888964707126665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72586095462592643138084443 108879143193888964707126665)
      ·
        refine ⟨81659357395416723530344999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108879143193888964707126665 81659357395416723530344999)
        ·
          refine ⟨122489036093125085295517499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81659357395416723530344999 122489036093125085295517499)
          ·
            refine ⟨183733554139687627943276249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122489036093125085295517499 183733554139687627943276249)
            ·
              refine ⟨137800165604765720957457187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183733554139687627943276249 137800165604765720957457187)
              ·
                refine ⟨206700248407148581436185781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137800165604765720957457187 206700248407148581436185781)
                ·
                  refine ⟨19378148288170179509642417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 206700248407148581436185781 19378148288170179509642417)
                  ·
                    refine ⟨14533611216127634632231813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19378148288170179509642417 14533611216127634632231813)
                    ·
                      refine ⟨2725052103023931493543465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14533611216127634632231813 2725052103023931493543465)
                      ·
                        rfl

theorem cell23_5307020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_5307020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307020 prefixEnd_5307020 := by exact prefixLift 5307020
  have htrace : WordTrace (prefixWord ++ tailWord_5307020) baseStart_5307020 baseEnd_5307020 := by
    simpa [prefixWord, tailWord_5307020, baseEnd_5307020] using wordTrace_append hprefix tailTrace_5307020
  have hstable : (prefixWord ++ tailWord_5307020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307020).length < 2 ^ (prefixWord ++ tailWord_5307020).sum := by decide
  have hdescent : baseEnd_5307020 < baseStart_5307020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307041 : List Nat := [1, 2, 3, 3, 3, 2, 1, 2, 1, 1, 4]
def baseStart_5307041 : Nat := 118140960795 + 5307041 * 2 ^ 59
def prefixEnd_5307041 : Nat := 4983230072969 + 3 ^ 40 * 5307041 * 2
def baseEnd_5307041 : Nat := 2725062886117675911380869

theorem tailTrace_5307041 : CollatzResearch.WordTrace tailWord_5307041 prefixEnd_5307041 2725062886117675911380869 := by
  unfold tailWord_5307041
  simp only [CollatzResearch.WordTrace]
  refine ⟨193563687166504302288072977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129042458111002868192048651 193563687166504302288072977)
  ·
    refine ⟨145172765374878226716054733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193563687166504302288072977 145172765374878226716054733)
    ·
      refine ⟨54439787015579335018520525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145172765374878226716054733 54439787015579335018520525)
      ·
        refine ⟨20414920130842250631945197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54439787015579335018520525 20414920130842250631945197)
        ·
          refine ⟨7655595049065843986979449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20414920130842250631945197 7655595049065843986979449)
          ·
            refine ⟨5741696286799382990234587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7655595049065843986979449 5741696286799382990234587)
            ·
              refine ⟨8612544430199074485351881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5741696286799382990234587 8612544430199074485351881)
              ·
                refine ⟨6459408322649305864013911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8612544430199074485351881 6459408322649305864013911)
                ·
                  refine ⟨9689112483973958796020867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6459408322649305864013911 9689112483973958796020867)
                  ·
                    refine ⟨14533668725960938194031301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9689112483973958796020867 14533668725960938194031301)
                    ·
                      refine ⟨2725062886117675911380869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14533668725960938194031301 2725062886117675911380869)
                      ·
                        rfl

theorem cell23_5307041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_5307041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307041 prefixEnd_5307041 := by exact prefixLift 5307041
  have htrace : WordTrace (prefixWord ++ tailWord_5307041) baseStart_5307041 baseEnd_5307041 := by
    simpa [prefixWord, tailWord_5307041, baseEnd_5307041] using wordTrace_append hprefix tailTrace_5307041
  have hstable : (prefixWord ++ tailWord_5307041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307041).length < 2 ^ (prefixWord ++ tailWord_5307041).sum := by decide
  have hdescent : baseEnd_5307041 < baseStart_5307041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307054 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_5307054 : Nat := 118140960795 + 5307054 * 2 ^ 59
def prefixEnd_5307054 : Nat := 4983230072969 + 3 ^ 40 * 5307054 * 2
def baseEnd_5307054 : Nat := 2725069561366184360518309

theorem tailTrace_5307054 : CollatzResearch.WordTrace tailWord_5307054 prefixEnd_5307054 2725069561366184360518309 := by
  unfold tailWord_5307054
  simp only [CollatzResearch.WordTrace]
  refine ⟨24195520164432150688537027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129042774210304803672197477 24195520164432150688537027)
  ·
    refine ⟨36293280246648226032805541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24195520164432150688537027 36293280246648226032805541)
    ·
      refine ⟨6804990046246542381151039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36293280246648226032805541 6804990046246542381151039)
      ·
        refine ⟨10207485069369813571726559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6804990046246542381151039 10207485069369813571726559)
        ·
          refine ⟨15311227604054720357589839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10207485069369813571726559 15311227604054720357589839)
          ·
            refine ⟨22966841406082080536384759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15311227604054720357589839 22966841406082080536384759)
            ·
              refine ⟨34450262109123120804577139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22966841406082080536384759 34450262109123120804577139)
              ·
                refine ⟨51675393163684681206865709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34450262109123120804577139 51675393163684681206865709)
                ·
                  refine ⟨19378272436381755452574641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51675393163684681206865709 19378272436381755452574641)
                  ·
                    refine ⟨14533704327286316589430981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19378272436381755452574641 14533704327286316589430981)
                    ·
                      refine ⟨2725069561366184360518309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14533704327286316589430981 2725069561366184360518309)
                      ·
                        rfl

theorem cell23_5307054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_5307054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307054 prefixEnd_5307054 := by exact prefixLift 5307054
  have htrace : WordTrace (prefixWord ++ tailWord_5307054) baseStart_5307054 baseEnd_5307054 := by
    simpa [prefixWord, tailWord_5307054, baseEnd_5307054] using wordTrace_append hprefix tailTrace_5307054
  have hstable : (prefixWord ++ tailWord_5307054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307054).length < 2 ^ (prefixWord ++ tailWord_5307054).sum := by decide
  have hdescent : baseEnd_5307054 < baseStart_5307054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307117 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_5307117 : Nat := 118140960795 + 5307117 * 2 ^ 59
def prefixEnd_5307117 : Nat := 4983230072969 + 3 ^ 40 * 5307117 * 2
def baseEnd_5307117 : Nat := 2725101910647417614030519

theorem tailTrace_5307117 : CollatzResearch.WordTrace tailWord_5307117 prefixEnd_5307117 2725101910647417614030519 := by
  unfold tailWord_5307117
  simp only [CollatzResearch.WordTrace]
  refine ⟨193566459114228967267839605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129044306076152644845226403 193566459114228967267839605)
  ·
    refine ⟨18146855541958965681359963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193566459114228967267839605 18146855541958965681359963)
    ·
      refine ⟨27220283312938448522039945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18146855541958965681359963 27220283312938448522039945)
      ·
        refine ⟨20415212484703836391529959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27220283312938448522039945 20415212484703836391529959)
        ·
          refine ⟨30622818727055754587294939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20415212484703836391529959 30622818727055754587294939)
          ·
            refine ⟨45934228090583631880942409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30622818727055754587294939 45934228090583631880942409)
            ·
              refine ⟨34450671067937723910706807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45934228090583631880942409 34450671067937723910706807)
              ·
                refine ⟨51676006601906585866060211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34450671067937723910706807 51676006601906585866060211)
                ·
                  refine ⟨77514009902859878799090317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51676006601906585866060211 77514009902859878799090317)
                  ·
                    refine ⟨29067753713572454549658869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77514009902859878799090317 29067753713572454549658869)
                    ·
                      refine ⟨2725101910647417614030519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29067753713572454549658869 2725101910647417614030519)
                      ·
                        rfl

theorem cell23_5307117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_5307117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307117 prefixEnd_5307117 := by exact prefixLift 5307117
  have htrace : WordTrace (prefixWord ++ tailWord_5307117) baseStart_5307117 baseEnd_5307117 := by
    simpa [prefixWord, tailWord_5307117, baseEnd_5307117] using wordTrace_append hprefix tailTrace_5307117
  have hstable : (prefixWord ++ tailWord_5307117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307117).length < 2 ^ (prefixWord ++ tailWord_5307117).sum := by decide
  have hdescent : baseEnd_5307117 < baseStart_5307117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307118 : List Nat := [4, 1, 2, 1, 1, 3, 4, 1, 1, 3, 2]
def baseStart_5307118 : Nat := 118140960795 + 5307118 * 2 ^ 59
def prefixEnd_5307118 : Nat := 4983230072969 + 3 ^ 40 * 5307118 * 2
def baseEnd_5307118 : Nat := 2725102424128072110118015

theorem tailTrace_5307118 : CollatzResearch.WordTrace tailWord_5307118 prefixEnd_5307118 2725102424128072110118015 := by
  unfold tailWord_5307118
  simp only [CollatzResearch.WordTrace]
  refine ⟨24195811948403168054828251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129044330391483562959084005 24195811948403168054828251)
  ·
    refine ⟨36293717922604752082242377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24195811948403168054828251 36293717922604752082242377)
    ·
      refine ⟨27220288441953564061681783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36293717922604752082242377 27220288441953564061681783)
      ·
        refine ⟨40830432662930346092522675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27220288441953564061681783 40830432662930346092522675)
        ·
          refine ⟨61245648994395519138784013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40830432662930346092522675 61245648994395519138784013)
          ·
            refine ⟨22967118372898319677044005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61245648994395519138784013 22967118372898319677044005)
            ·
              refine ⟨4306334694918434939445751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22967118372898319677044005 4306334694918434939445751)
              ·
                refine ⟨6459502042377652409168627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4306334694918434939445751 6459502042377652409168627)
                ·
                  refine ⟨9689253063566478613752941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6459502042377652409168627 9689253063566478613752941)
                  ·
                    refine ⟨3633469898837429480157353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9689253063566478613752941 3633469898837429480157353)
                    ·
                      refine ⟨2725102424128072110118015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3633469898837429480157353 2725102424128072110118015)
                      ·
                        rfl

theorem cell23_5307118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_5307118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307118 prefixEnd_5307118 := by exact prefixLift 5307118
  have htrace : WordTrace (prefixWord ++ tailWord_5307118) baseStart_5307118 baseEnd_5307118 := by
    simpa [prefixWord, tailWord_5307118, baseEnd_5307118] using wordTrace_append hprefix tailTrace_5307118
  have hstable : (prefixWord ++ tailWord_5307118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307118).length < 2 ^ (prefixWord ++ tailWord_5307118).sum := by decide
  have hdescent : baseEnd_5307118 < baseStart_5307118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307120 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 9]
def baseStart_5307120 : Nat := 118140960795 + 5307120 * 2 ^ 59
def prefixEnd_5307120 : Nat := 4983230072969 + 3 ^ 40 * 5307120 * 2
def baseEnd_5307120 : Nat := 302789272343264566921445

theorem tailTrace_5307120 : CollatzResearch.WordTrace tailWord_5307120 prefixEnd_5307120 302789272343264566921445 := by
  unfold tailWord_5307120
  simp only [CollatzResearch.WordTrace]
  refine ⟨96783284266609049390099407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129044379022145399186799209 96783284266609049390099407)
  ·
    refine ⟨145174926399913574085149111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96783284266609049390099407 145174926399913574085149111)
    ·
      refine ⟨217762389599870361127723667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145174926399913574085149111 217762389599870361127723667)
      ·
        refine ⟨326643584399805541691585501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217762389599870361127723667 326643584399805541691585501)
        ·
          refine ⟨122491344149927078134344563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326643584399805541691585501 122491344149927078134344563)
          ·
            refine ⟨183737016224890617201516845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122491344149927078134344563 183737016224890617201516845)
            ·
              refine ⟨68901381084333981450568817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 183737016224890617201516845 68901381084333981450568817)
              ·
                refine ⟨51676035813250486087926613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68901381084333981450568817 51676035813250486087926613)
                ·
                  refine ⟨302789272343264566921445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51676035813250486087926613 302789272343264566921445)
                  ·
                    rfl

theorem cell23_5307120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 9].length) (baseStart_5307120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307120 prefixEnd_5307120 := by exact prefixLift 5307120
  have htrace : WordTrace (prefixWord ++ tailWord_5307120) baseStart_5307120 baseEnd_5307120 := by
    simpa [prefixWord, tailWord_5307120, baseEnd_5307120] using wordTrace_append hprefix tailTrace_5307120
  have hstable : (prefixWord ++ tailWord_5307120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307120).length < 2 ^ (prefixWord ++ tailWord_5307120).sum := by decide
  have hdescent : baseEnd_5307120 < baseStart_5307120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307125 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_5307125 : Nat := 118140960795 + 5307125 * 2 ^ 59
def prefixEnd_5307125 : Nat := 4983230072969 + 3 ^ 40 * 5307125 * 2
def baseEnd_5307125 : Nat := 2725106018492653582730483

theorem tailTrace_5307125 : CollatzResearch.WordTrace tailWord_5307125 prefixEnd_5307125 2725106018492653582730483 := by
  unfold tailWord_5307125
  simp only [CollatzResearch.WordTrace]
  refine ⟨193566750898199984634130829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129044500598799989756087219 193566750898199984634130829)
  ·
    refine ⟨72587531586824994237799061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193566750898199984634130829 72587531586824994237799061)
    ·
      refine ⟨3402540543132421604896831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72587531586824994237799061 3402540543132421604896831)
      ·
        refine ⟨5103810814698632407345247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3402540543132421604896831 5103810814698632407345247)
        ·
          refine ⟨7655716222047948611017871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5103810814698632407345247 7655716222047948611017871)
          ·
            refine ⟨11483574333071922916526807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7655716222047948611017871 11483574333071922916526807)
            ·
              refine ⟨17225361499607884374790211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11483574333071922916526807 17225361499607884374790211)
              ·
                refine ⟨25838042249411826562185317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17225361499607884374790211 25838042249411826562185317)
                ·
                  refine ⟨4844632921764717480409747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25838042249411826562185317 4844632921764717480409747)
                  ·
                    refine ⟨7266949382647076220614621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4844632921764717480409747 7266949382647076220614621)
                    ·
                      refine ⟨2725106018492653582730483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7266949382647076220614621 2725106018492653582730483)
                      ·
                        rfl

theorem cell23_5307125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_5307125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307125 prefixEnd_5307125 := by exact prefixLift 5307125
  have htrace : WordTrace (prefixWord ++ tailWord_5307125) baseStart_5307125 baseEnd_5307125 := by
    simpa [prefixWord, tailWord_5307125, baseEnd_5307125] using wordTrace_append hprefix tailTrace_5307125
  have hstable : (prefixWord ++ tailWord_5307125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307125).length < 2 ^ (prefixWord ++ tailWord_5307125).sum := by decide
  have hdescent : baseEnd_5307125 < baseStart_5307125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307167 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 1, 7]
def baseStart_5307167 : Nat := 118140960795 + 5307167 * 2 ^ 59
def prefixEnd_5307167 : Nat := 4983230072969 + 3 ^ 40 * 5307167 * 2
def baseEnd_5307167 : Nat := 908375861560047472801763

theorem tailTrace_5307167 : CollatzResearch.WordTrace tailWord_5307167 prefixEnd_5307167 908375861560047472801763 := by
  unfold tailWord_5307167
  simp only [CollatzResearch.WordTrace]
  refine ⟨193568282764047825807159755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129045521842698550538106503 193568282764047825807159755)
  ·
    refine ⟨290352424146071738710739633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193568282764047825807159755 290352424146071738710739633)
    ·
      refine ⟨217764318109553804033054725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290352424146071738710739633 217764318109553804033054725)
      ·
        refine ⟨40830809645541338256197761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217764318109553804033054725 40830809645541338256197761)
        ·
          refine ⟨30623107234156003692148321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40830809645541338256197761 30623107234156003692148321)
          ·
            refine ⟨22967330425617002769111241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30623107234156003692148321 22967330425617002769111241)
            ·
              refine ⟨17225497819212752076833431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22967330425617002769111241 17225497819212752076833431)
              ·
                refine ⟨25838246728819128115250147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17225497819212752076833431 25838246728819128115250147)
                ·
                  refine ⟨38757370093228692172875221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25838246728819128115250147 38757370093228692172875221)
                  ·
                    refine ⟨908375861560047472801763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38757370093228692172875221 908375861560047472801763)
                    ·
                      rfl

theorem cell23_5307167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 7].length) (baseStart_5307167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307167 prefixEnd_5307167 := by exact prefixLift 5307167
  have htrace : WordTrace (prefixWord ++ tailWord_5307167) baseStart_5307167 baseEnd_5307167 := by
    simpa [prefixWord, tailWord_5307167, baseEnd_5307167] using wordTrace_append hprefix tailTrace_5307167
  have hstable : (prefixWord ++ tailWord_5307167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307167).length < 2 ^ (prefixWord ++ tailWord_5307167).sum := by decide
  have hdescent : baseEnd_5307167 < baseStart_5307167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307188 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 7]
def baseStart_5307188 : Nat := 118140960795 + 5307188 * 2 ^ 59
def prefixEnd_5307188 : Nat := 4983230072969 + 3 ^ 40 * 5307188 * 2
def baseEnd_5307188 : Nat := 302793151974876315138077

theorem tailTrace_5307188 : CollatzResearch.WordTrace tailWord_5307188 prefixEnd_5307188 302793151974876315138077 := by
  unfold tailWord_5307188
  simp only [CollatzResearch.WordTrace]
  refine ⟨96784524348485873196837109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129046032464647830929116145 96784524348485873196837109)
  ·
    refine ⟨9073549157670550612203479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96784524348485873196837109 9073549157670550612203479)
    ·
      refine ⟨13610323736505825918305219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9073549157670550612203479 13610323736505825918305219)
      ·
        refine ⟨20415485604758738877457829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13610323736505825918305219 20415485604758738877457829)
        ·
          refine ⟨3827903550892263539523343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20415485604758738877457829 3827903550892263539523343)
          ·
            refine ⟨5741855326338395309285015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3827903550892263539523343 5741855326338395309285015)
            ·
              refine ⟨8612782989507592963927523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5741855326338395309285015 8612782989507592963927523)
              ·
                refine ⟨12919174484261389445891285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8612782989507592963927523 12919174484261389445891285)
                ·
                  refine ⟨302793151974876315138077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12919174484261389445891285 302793151974876315138077)
                  ·
                    rfl

theorem cell23_5307188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_5307188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307188 prefixEnd_5307188 := by exact prefixLift 5307188
  have htrace : WordTrace (prefixWord ++ tailWord_5307188) baseStart_5307188 baseEnd_5307188 := by
    simpa [prefixWord, tailWord_5307188, baseEnd_5307188] using wordTrace_append hprefix tailTrace_5307188
  have hstable : (prefixWord ++ tailWord_5307188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307188).length < 2 ^ (prefixWord ++ tailWord_5307188).sum := by decide
  have hdescent : baseEnd_5307188 < baseStart_5307188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307194 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5]
def baseStart_5307194 : Nat := 118140960795 + 5307194 * 2 ^ 59
def prefixEnd_5307194 : Nat := 4983230072969 + 3 ^ 40 * 5307194 * 2
def baseEnd_5307194 : Nat := 2725141448657813812767665

theorem tailTrace_5307194 : CollatzResearch.WordTrace tailWord_5307194 prefixEnd_5307194 2725141448657813812767665 := by
  unfold tailWord_5307194
  simp only [CollatzResearch.WordTrace]
  refine ⟨48392316883737502354598159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129046178356633339612261757 48392316883737502354598159)
  ·
    refine ⟨72588475325606253531897239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48392316883737502354598159 72588475325606253531897239)
    ·
      refine ⟨108882712988409380297845859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72588475325606253531897239 108882712988409380297845859)
      ·
        refine ⟨163324069482614070446768789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108882712988409380297845859 163324069482614070446768789)
        ·
          refine ⟨7655815756997534552192287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 163324069482614070446768789 7655815756997534552192287)
          ·
            refine ⟨11483723635496301828288431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7655815756997534552192287 11483723635496301828288431)
            ·
              refine ⟨17225585453244452742432647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11483723635496301828288431 17225585453244452742432647)
              ·
                refine ⟨25838378179866679113648971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17225585453244452742432647 25838378179866679113648971)
                ·
                  refine ⟨38757567269800018670473457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25838378179866679113648971 38757567269800018670473457)
                  ·
                    refine ⟨29068175452350014002855093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38757567269800018670473457 29068175452350014002855093)
                    ·
                      refine ⟨2725141448657813812767665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29068175452350014002855093 2725141448657813812767665)
                      ·
                        rfl

theorem cell23_5307194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_5307194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307194 prefixEnd_5307194 := by exact prefixLift 5307194
  have htrace : WordTrace (prefixWord ++ tailWord_5307194) baseStart_5307194 baseEnd_5307194 := by
    simpa [prefixWord, tailWord_5307194, baseEnd_5307194] using wordTrace_append hprefix tailTrace_5307194
  have hstable : (prefixWord ++ tailWord_5307194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307194).length < 2 ^ (prefixWord ++ tailWord_5307194).sum := by decide
  have hdescent : baseEnd_5307194 < baseStart_5307194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307214 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 3, 4]
def baseStart_5307214 : Nat := 118140960795 + 5307214 * 2 ^ 59
def prefixEnd_5307214 : Nat := 4983230072969 + 3 ^ 40 * 5307214 * 2
def baseEnd_5307214 : Nat := 908383906090301244839191

theorem tailTrace_5307214 : CollatzResearch.WordTrace tailWord_5307214 prefixEnd_5307214 908383906090301244839191 := by
  unfold tailWord_5307214
  simp only [CollatzResearch.WordTrace]
  refine ⟨24196249624359694104265087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129046664663251701889413797 24196249624359694104265087)
  ·
    refine ⟨36294374436539541156397631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24196249624359694104265087 36294374436539541156397631)
    ·
      refine ⟨54441561654809311734596447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36294374436539541156397631 54441561654809311734596447)
      ·
        refine ⟨81662342482213967601894671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54441561654809311734596447 81662342482213967601894671)
        ·
          refine ⟨122493513723320951402842007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81662342482213967601894671 122493513723320951402842007)
          ·
            refine ⟨183740270584981427104263011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122493513723320951402842007 183740270584981427104263011)
            ·
              refine ⟨275610405877472140656394517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183740270584981427104263011 275610405877472140656394517)
              ·
                refine ⟨12919237775506506593268493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 275610405877472140656394517 12919237775506506593268493)
                ·
                  refine ⟨4844714165814939972475685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12919237775506506593268493 4844714165814939972475685)
                  ·
                    refine ⟨908383906090301244839191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4844714165814939972475685 908383906090301244839191)
                    ·
                      rfl

theorem cell23_5307214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_5307214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307214 prefixEnd_5307214 := by exact prefixLift 5307214
  have htrace : WordTrace (prefixWord ++ tailWord_5307214) baseStart_5307214 baseEnd_5307214 := by
    simpa [prefixWord, tailWord_5307214, baseEnd_5307214] using wordTrace_append hprefix tailTrace_5307214
  have hstable : (prefixWord ++ tailWord_5307214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307214).length < 2 ^ (prefixWord ++ tailWord_5307214).sum := by decide
  have hdescent : baseEnd_5307214 < baseStart_5307214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307231 : List Nat := [1, 1, 2, 3, 1, 3, 2, 5, 1, 4]
def baseStart_5307231 : Nat := 118140960795 + 5307231 * 2 ^ 59
def prefixEnd_5307231 : Nat := 4983230072969 + 3 ^ 40 * 5307231 * 2
def baseEnd_5307231 : Nat := 908386815814010056001665

theorem tailTrace_5307231 : CollatzResearch.WordTrace tailWord_5307231 prefixEnd_5307231 908386815814010056001665 := by
  unfold tailWord_5307231
  simp only [CollatzResearch.WordTrace]
  refine ⟨193570617035815964737489547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129047078023877309824993031 193570617035815964737489547)
  ·
    refine ⟨290355925553723947106234321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193570617035815964737489547 290355925553723947106234321)
    ·
      refine ⟨217766944165292960329675741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290355925553723947106234321 217766944165292960329675741)
      ·
        refine ⟨81662604061984860123628403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217766944165292960329675741 81662604061984860123628403)
        ·
          refine ⟨122493906092977290185442605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81662604061984860123628403 122493906092977290185442605)
          ·
            refine ⟨45935214784866483819540977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122493906092977290185442605 45935214784866483819540977)
            ·
              refine ⟨34451411088649862864655733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45935214784866483819540977 34451411088649862864655733)
              ·
                refine ⟨3229819789560924643561475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34451411088649862864655733 3229819789560924643561475)
                ·
                  refine ⟨4844729684341386965342213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3229819789560924643561475 4844729684341386965342213)
                  ·
                    refine ⟨908386815814010056001665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4844729684341386965342213 908386815814010056001665)
                    ·
                      rfl

theorem cell23_5307231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 5, 1, 4].length) (baseStart_5307231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307231 prefixEnd_5307231 := by exact prefixLift 5307231
  have htrace : WordTrace (prefixWord ++ tailWord_5307231) baseStart_5307231 baseEnd_5307231 := by
    simpa [prefixWord, tailWord_5307231, baseEnd_5307231] using wordTrace_append hprefix tailTrace_5307231
  have hstable : (prefixWord ++ tailWord_5307231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307231).length < 2 ^ (prefixWord ++ tailWord_5307231).sum := by decide
  have hdescent : baseEnd_5307231 < baseStart_5307231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307244 : List Nat := [2, 2, 1, 1, 4, 1, 4, 2, 6]
def baseStart_5307244 : Nat := 118140960795 + 5307244 * 2 ^ 59
def prefixEnd_5307244 : Nat := 4983230072969 + 3 ^ 40 * 5307244 * 2
def baseEnd_5307244 : Nat := 302796346965615401904715

theorem tailTrace_5307244 : CollatzResearch.WordTrace tailWord_5307244 prefixEnd_5307244 302796346965615401904715 := by
  unfold tailWord_5307244
  simp only [CollatzResearch.WordTrace]
  refine ⟨96785545592384433978856393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129047394123179245305141857 96785545592384433978856393)
  ·
    refine ⟨72589159194288325484142295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96785545592384433978856393 72589159194288325484142295)
    ·
      refine ⟨108883738791432488226213443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72589159194288325484142295 108883738791432488226213443)
      ·
        refine ⟨163325608187148732339320165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108883738791432488226213443 163325608187148732339320165)
        ·
          refine ⟨30623551535090387313622531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163325608187148732339320165 30623551535090387313622531)
          ·
            refine ⟨45935327302635580970433797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30623551535090387313622531 45935327302635580970433797)
            ·
              refine ⟨8612873869244171431956337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45935327302635580970433797 8612873869244171431956337)
              ·
                refine ⟨6459655401933128573967253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8612873869244171431956337 6459655401933128573967253)
                ·
                  refine ⟨302796346965615401904715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6459655401933128573967253 302796346965615401904715)
                  ·
                    rfl

theorem cell23_5307244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 6].length) (baseStart_5307244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307244 prefixEnd_5307244 := by exact prefixLift 5307244
  have htrace : WordTrace (prefixWord ++ tailWord_5307244) baseStart_5307244 baseEnd_5307244 := by
    simpa [prefixWord, tailWord_5307244, baseEnd_5307244] using wordTrace_append hprefix tailTrace_5307244
  have hstable : (prefixWord ++ tailWord_5307244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307244).length < 2 ^ (prefixWord ++ tailWord_5307244).sum := by decide
  have hdescent : baseEnd_5307244 < baseStart_5307244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307248 : List Nat := [2, 1, 1, 1, 4, 1, 6, 2, 1, 4]
def baseStart_5307248 : Nat := 118140960795 + 5307248 * 2 ^ 59
def prefixEnd_5307248 : Nat := 4983230072969 + 3 ^ 40 * 5307248 * 2
def baseEnd_5307248 : Nat := 908389725537718867164139

theorem tailTrace_5307248 : CollatzResearch.WordTrace tailWord_5307248 prefixEnd_5307248 908389725537718867164139 := by
  unfold tailWord_5307248
  simp only [CollatzResearch.WordTrace]
  refine ⟨96785618538377188320429199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129047491384502917760572265 96785618538377188320429199)
  ·
    refine ⟨145178427807565782480643799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96785618538377188320429199 145178427807565782480643799)
    ·
      refine ⟨217767641711348673720965699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145178427807565782480643799 217767641711348673720965699)
      ·
        refine ⟨326651462567023010581448549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217767641711348673720965699 326651462567023010581448549)
        ·
          refine ⟨61247149231316814484021603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 326651462567023010581448549 61247149231316814484021603)
          ·
            refine ⟨91870723846975221726032405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61247149231316814484021603 91870723846975221726032405)
            ·
              refine ⟨4306440180326963518407769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91870723846975221726032405 4306440180326963518407769)
              ·
                refine ⟨3229830135245222638805827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4306440180326963518407769 3229830135245222638805827)
                ·
                  refine ⟨4844745202867833958208741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3229830135245222638805827 4844745202867833958208741)
                  ·
                    refine ⟨908389725537718867164139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4844745202867833958208741 908389725537718867164139)
                    ·
                      rfl

theorem cell23_5307248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 2, 1, 4].length) (baseStart_5307248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307248 prefixEnd_5307248 := by exact prefixLift 5307248
  have htrace : WordTrace (prefixWord ++ tailWord_5307248) baseStart_5307248 baseEnd_5307248 := by
    simpa [prefixWord, tailWord_5307248, baseEnd_5307248] using wordTrace_append hprefix tailTrace_5307248
  have hstable : (prefixWord ++ tailWord_5307248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307248).length < 2 ^ (prefixWord ++ tailWord_5307248).sum := by decide
  have hdescent : baseEnd_5307248 < baseStart_5307248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307267 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 7]
def baseStart_5307267 : Nat := 118140960795 + 5307267 * 2 ^ 59
def prefixEnd_5307267 : Nat := 4983230072969 + 3 ^ 40 * 5307267 * 2
def baseEnd_5307267 : Nat := 2725178932745592027154829

theorem tailTrace_5307267 : CollatzResearch.WordTrace tailWord_5307267 prefixEnd_5307267 2725178932745592027154829 := by
  unfold tailWord_5307267
  simp only [CollatzResearch.WordTrace]
  refine ⟨193571930063685542885800055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129047953375790361923866703 193571930063685542885800055)
  ·
    refine ⟨290357895095528314328700083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193571930063685542885800055 290357895095528314328700083)
    ·
      refine ⟨435536842643292471493050125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290357895095528314328700083 435536842643292471493050125)
      ·
        refine ⟨163326315991234676809893797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435536842643292471493050125 163326315991234676809893797)
        ·
          refine ⟨30623684248356501901855087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163326315991234676809893797 30623684248356501901855087)
          ·
            refine ⟨45935526372534752852782631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30623684248356501901855087 45935526372534752852782631)
            ·
              refine ⟨68903289558802129279173947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45935526372534752852782631 68903289558802129279173947)
              ·
                refine ⟨103354934338203193918760921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68903289558802129279173947 103354934338203193918760921)
                ·
                  refine ⟨77516200753652395439070691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103354934338203193918760921 77516200753652395439070691)
                  ·
                    refine ⟨116274301130478593158606037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77516200753652395439070691 116274301130478593158606037)
                    ·
                      refine ⟨2725178932745592027154829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116274301130478593158606037 2725178932745592027154829)
                      ·
                        rfl

theorem cell23_5307267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_5307267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307267 prefixEnd_5307267 := by exact prefixLift 5307267
  have htrace : WordTrace (prefixWord ++ tailWord_5307267) baseStart_5307267 baseEnd_5307267 := by
    simpa [prefixWord, tailWord_5307267, baseEnd_5307267] using wordTrace_append hprefix tailTrace_5307267
  have hstable : (prefixWord ++ tailWord_5307267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307267).length < 2 ^ (prefixWord ++ tailWord_5307267).sum := by decide
  have hdescent : baseEnd_5307267 < baseStart_5307267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307271 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 5, 1, 3]
def baseStart_5307271 : Nat := 118140960795 + 5307271 * 2 ^ 59
def prefixEnd_5307271 : Nat := 4983230072969 + 3 ^ 40 * 5307271 * 2
def baseEnd_5307271 : Nat := 2725180986668210011504811

theorem tailTrace_5307271 : CollatzResearch.WordTrace tailWord_5307271 prefixEnd_5307271 2725180986668210011504811 := by
  unfold tailWord_5307271
  simp only [CollatzResearch.WordTrace]
  refine ⟨193572075955671051568945667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129048050637114034379297111 193572075955671051568945667)
  ·
    refine ⟨290358113933506577353418501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193572075955671051568945667 290358113933506577353418501)
    ·
      refine ⟨54442146362532483253765969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290358113933506577353418501 54442146362532483253765969)
      ·
        refine ⟨40831609771899362440324477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54442146362532483253765969 40831609771899362440324477)
        ·
          refine ⟨15311853664462260915121679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40831609771899362440324477 15311853664462260915121679)
          ·
            refine ⟨22967780496693391372682519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15311853664462260915121679 22967780496693391372682519)
            ·
              refine ⟨34451670745040087059023779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22967780496693391372682519 34451670745040087059023779)
              ·
                refine ⟨51677506117560130588535669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34451670745040087059023779 51677506117560130588535669)
                ·
                  refine ⟨4844766198521262242675219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51677506117560130588535669 4844766198521262242675219)
                  ·
                    refine ⟨7267149297781893364012829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4844766198521262242675219 7267149297781893364012829)
                    ·
                      refine ⟨2725180986668210011504811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7267149297781893364012829 2725180986668210011504811)
                      ·
                        rfl

theorem cell23_5307271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_5307271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307271 prefixEnd_5307271 := by exact prefixLift 5307271
  have htrace : WordTrace (prefixWord ++ tailWord_5307271) baseStart_5307271 baseEnd_5307271 := by
    simpa [prefixWord, tailWord_5307271, baseEnd_5307271] using wordTrace_append hprefix tailTrace_5307271
  have hstable : (prefixWord ++ tailWord_5307271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307271).length < 2 ^ (prefixWord ++ tailWord_5307271).sum := by decide
  have hdescent : baseEnd_5307271 < baseStart_5307271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307307 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 6]
def baseStart_5307307 : Nat := 118140960795 + 5307307 * 2 ^ 59
def prefixEnd_5307307 : Nat := 4983230072969 + 3 ^ 40 * 5307307 * 2
def baseEnd_5307307 : Nat := 2725199471971771870654645

theorem tailTrace_5307307 : CollatzResearch.WordTrace tailWord_5307307 prefixEnd_5307307 2725199471971771870654645 := by
  unfold tailWord_5307307
  simp only [CollatzResearch.WordTrace]
  refine ⟨193573388983540629717256175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129048925989027086478170783 193573388983540629717256175)
  ·
    refine ⟨290360083475310944575884263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193573388983540629717256175 290360083475310944575884263)
    ·
      refine ⟨435540125212966416863826395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290360083475310944575884263 435540125212966416863826395)
      ·
        refine ⟨653310187819449625295739593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435540125212966416863826395 653310187819449625295739593)
        ·
          refine ⟨489982640864587218971804695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 653310187819449625295739593 489982640864587218971804695)
          ·
            refine ⟨734973961296880828457707043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489982640864587218971804695 734973961296880828457707043)
            ·
              refine ⟨1102460941945321242686560565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734973961296880828457707043 1102460941945321242686560565)
              ·
                refine ⟨103355713307373866501865053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1102460941945321242686560565 103355713307373866501865053)
                ·
                  refine ⟨38758392490265199938199395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103355713307373866501865053 38758392490265199938199395)
                  ·
                    refine ⟨58137588735397799907299093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38758392490265199938199395 58137588735397799907299093)
                    ·
                      refine ⟨2725199471971771870654645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58137588735397799907299093 2725199471971771870654645)
                      ·
                        rfl

theorem cell23_5307307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 6].length) (baseStart_5307307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307307 prefixEnd_5307307 := by exact prefixLift 5307307
  have htrace : WordTrace (prefixWord ++ tailWord_5307307) baseStart_5307307 baseEnd_5307307 := by
    simpa [prefixWord, tailWord_5307307, baseEnd_5307307] using wordTrace_append hprefix tailTrace_5307307
  have hstable : (prefixWord ++ tailWord_5307307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307307).length < 2 ^ (prefixWord ++ tailWord_5307307).sum := by decide
  have hdescent : baseEnd_5307307 < baseStart_5307307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307321 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 1, 6]
def baseStart_5307321 : Nat := 118140960795 + 5307321 * 2 ^ 59
def prefixEnd_5307321 : Nat := 4983230072969 + 3 ^ 40 * 5307321 * 2
def baseEnd_5307321 : Nat := 908402220233644938626527

theorem tailTrace_5307321 : CollatzResearch.WordTrace tailWord_5307321 prefixEnd_5307321 908402220233644938626527 := by
  unfold tailWord_5307321
  simp only [CollatzResearch.WordTrace]
  refine ⟨193573899605489910108265817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129049266403659940072177211 193573899605489910108265817)
  ·
    refine ⟨145180424704117432581199363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193573899605489910108265817 145180424704117432581199363)
    ·
      refine ⟨217770637056176148871799045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145180424704117432581199363 217770637056176148871799045)
      ·
        refine ⟨40831994448033027913462321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217770637056176148871799045 40831994448033027913462321)
        ·
          refine ⟨30623995836024770935096741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40831994448033027913462321 30623995836024770935096741)
          ·
            refine ⟨5741999219254644550330639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30623995836024770935096741 5741999219254644550330639)
            ·
              refine ⟨8612998828881966825495959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5741999219254644550330639 8612998828881966825495959)
              ·
                refine ⟨12919498243322950238243939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8612998828881966825495959 12919498243322950238243939)
                ·
                  refine ⟨19379247364984425357365909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12919498243322950238243939 19379247364984425357365909)
                  ·
                    refine ⟨908402220233644938626527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19379247364984425357365909 908402220233644938626527)
                    ·
                      rfl

theorem cell23_5307321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 6].length) (baseStart_5307321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307321 prefixEnd_5307321 := by exact prefixLift 5307321
  have htrace : WordTrace (prefixWord ++ tailWord_5307321) baseStart_5307321 baseEnd_5307321 := by
    simpa [prefixWord, tailWord_5307321, baseEnd_5307321] using wordTrace_append hprefix tailTrace_5307321
  have hstable : (prefixWord ++ tailWord_5307321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307321).length < 2 ^ (prefixWord ++ tailWord_5307321).sum := by decide
  have hdescent : baseEnd_5307321 < baseStart_5307321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307328 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 3, 2, 2]
def baseStart_5307328 : Nat := 118140960795 + 5307328 * 2 ^ 59
def prefixEnd_5307328 : Nat := 4983230072969 + 3 ^ 40 * 5307328 * 2
def baseEnd_5307328 : Nat := 2725210255065516288492049

theorem tailTrace_5307328 : CollatzResearch.WordTrace tailWord_5307328 prefixEnd_5307328 2725210255065516288492049 := by
  unfold tailWord_5307328
  simp only [CollatzResearch.WordTrace]
  refine ⟨96787077458232275151885319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129049436610976366869180425 96787077458232275151885319)
  ·
    refine ⟨145180616187348412727827979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96787077458232275151885319 145180616187348412727827979)
    ·
      refine ⟨217770924281022619091741969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145180616187348412727827979 217770924281022619091741969)
      ·
        refine ⟨163328193210766964318806477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217770924281022619091741969 163328193210766964318806477)
        ·
          refine ⟨61248072454037611619552429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163328193210766964318806477 61248072454037611619552429)
          ·
            refine ⟨22968027170264104357332161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61248072454037611619552429 22968027170264104357332161)
            ·
              refine ⟨17226020377698078267999121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22968027170264104357332161 17226020377698078267999121)
              ·
                refine ⟨12919515283273558700999341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17226020377698078267999121 12919515283273558700999341)
                ·
                  refine ⟨4844818231227584512874753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12919515283273558700999341 4844818231227584512874753)
                  ·
                    refine ⟨3633613673420688384656065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4844818231227584512874753 3633613673420688384656065)
                    ·
                      refine ⟨2725210255065516288492049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3633613673420688384656065 2725210255065516288492049)
                      ·
                        rfl

theorem cell23_5307328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 3, 2, 2].length) (baseStart_5307328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307328 prefixEnd_5307328 := by exact prefixLift 5307328
  have htrace : WordTrace (prefixWord ++ tailWord_5307328) baseStart_5307328 baseEnd_5307328 := by
    simpa [prefixWord, tailWord_5307328, baseEnd_5307328] using wordTrace_append hprefix tailTrace_5307328
  have hstable : (prefixWord ++ tailWord_5307328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307328).length < 2 ^ (prefixWord ++ tailWord_5307328).sum := by decide
  have hdescent : baseEnd_5307328 < baseStart_5307328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307344 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 3]
def baseStart_5307344 : Nat := 118140960795 + 5307344 * 2 ^ 59
def prefixEnd_5307344 : Nat := 4983230072969 + 3 ^ 40 * 5307344 * 2
def baseEnd_5307344 : Nat := 2725218470755988225891975

theorem tailTrace_5307344 : CollatzResearch.WordTrace tailWord_5307344 prefixEnd_5307344 2725218470755988225891975 := by
  unfold tailWord_5307344
  simp only [CollatzResearch.WordTrace]
  refine ⟨96787369242203292518176543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129049825656271056690902057 96787369242203292518176543)
  ·
    refine ⟨145181053863304938777264815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96787369242203292518176543 145181053863304938777264815)
    ·
      refine ⟨217771580794957408165897223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145181053863304938777264815 217771580794957408165897223)
      ·
        refine ⟨326657371192436112248845835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217771580794957408165897223 326657371192436112248845835)
        ·
          refine ⟨489986056788654168373268753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326657371192436112248845835 489986056788654168373268753)
          ·
            refine ⟨367489542591490626279951565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489986056788654168373268753 367489542591490626279951565)
            ·
              refine ⟨137808578471808984854981837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 367489542591490626279951565 137808578471808984854981837)
              ·
                refine ⟨51678216926928369320618189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137808578471808984854981837 51678216926928369320618189)
                ·
                  refine ⟨19379331347598138495231821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51678216926928369320618189 19379331347598138495231821)
                  ·
                    refine ⟨7267249255349301935711933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19379331347598138495231821 7267249255349301935711933)
                    ·
                      refine ⟨2725218470755988225891975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7267249255349301935711933 2725218470755988225891975)
                      ·
                        rfl

theorem cell23_5307344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 3].length) (baseStart_5307344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307344 prefixEnd_5307344 := by exact prefixLift 5307344
  have htrace : WordTrace (prefixWord ++ tailWord_5307344) baseStart_5307344 baseEnd_5307344 := by
    simpa [prefixWord, tailWord_5307344, baseEnd_5307344] using wordTrace_append hprefix tailTrace_5307344
  have hstable : (prefixWord ++ tailWord_5307344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307344).length < 2 ^ (prefixWord ++ tailWord_5307344).sum := by decide
  have hdescent : baseEnd_5307344 < baseStart_5307344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307348 : List Nat := [2, 4, 1, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_5307348 : Nat := 118140960795 + 5307348 * 2 ^ 59
def prefixEnd_5307348 : Nat := 4983230072969 + 3 ^ 40 * 5307348 * 2
def baseEnd_5307348 : Nat := 2725220524678606210241957

theorem tailTrace_5307348 : CollatzResearch.WordTrace tailWord_5307348 prefixEnd_5307348 2725220524678606210241957 := by
  unfold tailWord_5307348
  simp only [CollatzResearch.WordTrace]
  refine ⟨96787442188196046859749349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129049922917594729146332465 96787442188196046859749349)
  ·
    refine ⟨18147645410286758786203003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96787442188196046859749349 18147645410286758786203003)
    ·
      refine ⟨27221468115430138179304505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18147645410286758786203003 27221468115430138179304505)
      ·
        refine ⟨20416101086572603634478379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27221468115430138179304505 20416101086572603634478379)
        ·
          refine ⟨30624151629858905451717569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20416101086572603634478379 30624151629858905451717569)
          ·
            refine ⟨22968113722394179088788177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30624151629858905451717569 22968113722394179088788177)
            ·
              refine ⟨17226085291795634316591133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22968113722394179088788177 17226085291795634316591133)
              ·
                refine ⟨6459781984423362868721675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17226085291795634316591133 6459781984423362868721675)
                ·
                  refine ⟨9689672976635044303082513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6459781984423362868721675 9689672976635044303082513)
                  ·
                    refine ⟨7267254732476283227311885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9689672976635044303082513 7267254732476283227311885)
                    ·
                      refine ⟨2725220524678606210241957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7267254732476283227311885 2725220524678606210241957)
                      ·
                        rfl

theorem cell23_5307348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_5307348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307348 prefixEnd_5307348 := by exact prefixLift 5307348
  have htrace : WordTrace (prefixWord ++ tailWord_5307348) baseStart_5307348 baseEnd_5307348 := by
    simpa [prefixWord, tailWord_5307348, baseEnd_5307348] using wordTrace_append hprefix tailTrace_5307348
  have hstable : (prefixWord ++ tailWord_5307348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307348).length < 2 ^ (prefixWord ++ tailWord_5307348).sum := by decide
  have hdescent : baseEnd_5307348 < baseStart_5307348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307362 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_5307362 : Nat := 118140960795 + 5307362 * 2 ^ 59
def prefixEnd_5307362 : Nat := 4983230072969 + 3 ^ 40 * 5307362 * 2
def baseEnd_5307362 : Nat := 2725227713407769155466893

theorem tailTrace_5307362 : CollatzResearch.WordTrace tailWord_5307362 prefixEnd_5307362 2725227713407769155466893 := by
  unfold tailWord_5307362
  simp only [CollatzResearch.WordTrace]
  refine ⟨48393848749585343527627085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129050263332227582740338893 48393848749585343527627085)
  ·
    refine ⟨18147693281094503822860157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48393848749585343527627085 18147693281094503822860157)
    ·
      refine ⟨6805384980410438933572559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18147693281094503822860157 6805384980410438933572559)
      ·
        refine ⟨10208077470615658400358839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6805384980410438933572559 10208077470615658400358839)
        ·
          refine ⟨15312116205923487600538259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10208077470615658400358839 15312116205923487600538259)
          ·
            refine ⟨22968174308885231400807389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15312116205923487600538259 22968174308885231400807389)
            ·
              refine ⟨8613065365831961775302771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22968174308885231400807389 8613065365831961775302771)
              ·
                refine ⟨12919598048747942662954157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8613065365831961775302771 12919598048747942662954157)
                ·
                  refine ⟨4844849268280478498607809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12919598048747942662954157 4844849268280478498607809)
                  ·
                    refine ⟨3633636951210358873955857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4844849268280478498607809 3633636951210358873955857)
                    ·
                      refine ⟨2725227713407769155466893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3633636951210358873955857 2725227713407769155466893)
                      ·
                        rfl

theorem cell23_5307362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_5307362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307362 prefixEnd_5307362 := by exact prefixLift 5307362
  have htrace : WordTrace (prefixWord ++ tailWord_5307362) baseStart_5307362 baseEnd_5307362 := by
    simpa [prefixWord, tailWord_5307362, baseEnd_5307362] using wordTrace_append hprefix tailTrace_5307362
  have hstable : (prefixWord ++ tailWord_5307362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307362).length < 2 ^ (prefixWord ++ tailWord_5307362).sum := by decide
  have hdescent : baseEnd_5307362 < baseStart_5307362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307388 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 3, 3, 2]
def baseStart_5307388 : Nat := 118140960795 + 5307388 * 2 ^ 59
def prefixEnd_5307388 : Nat := 4983230072969 + 3 ^ 40 * 5307388 * 2
def baseEnd_5307388 : Nat := 2725241063904786053741773

theorem tailTrace_5307388 : CollatzResearch.WordTrace tailWord_5307388 prefixEnd_5307388 2725241063904786053741773 := by
  unfold tailWord_5307388
  simp only [CollatzResearch.WordTrace]
  refine ⟨96788171648123590275477409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129050895530831453700636545 96788171648123590275477409)
  ·
    refine ⟨72591128736092692706608057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96788171648123590275477409 72591128736092692706608057)
    ·
      refine ⟨54443346552069519529956043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72591128736092692706608057 54443346552069519529956043)
      ·
        refine ⟨81665019828104279294934065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54443346552069519529956043 81665019828104279294934065)
        ·
          refine ⟨61248764871078209471200549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81665019828104279294934065 61248764871078209471200549)
          ·
            refine ⟨11484143413327164275850103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61248764871078209471200549 11484143413327164275850103)
            ·
              refine ⟨17226215119990746413775155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11484143413327164275850103 17226215119990746413775155)
              ·
                refine ⟨25839322679986119620662733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17226215119990746413775155 25839322679986119620662733)
                ·
                  refine ⟨9689746004994794857748525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25839322679986119620662733 9689746004994794857748525)
                  ·
                    refine ⟨3633654751873048071655697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9689746004994794857748525 3633654751873048071655697)
                    ·
                      refine ⟨2725241063904786053741773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3633654751873048071655697 2725241063904786053741773)
                      ·
                        rfl

theorem cell23_5307388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_5307388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307388 prefixEnd_5307388 := by exact prefixLift 5307388
  have htrace : WordTrace (prefixWord ++ tailWord_5307388) baseStart_5307388 baseEnd_5307388 := by
    simpa [prefixWord, tailWord_5307388, baseEnd_5307388] using wordTrace_append hprefix tailTrace_5307388
  have hstable : (prefixWord ++ tailWord_5307388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307388).length < 2 ^ (prefixWord ++ tailWord_5307388).sum := by decide
  have hdescent : baseEnd_5307388 < baseStart_5307388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307469 : List Nat := [1, 6, 1, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_5307469 : Nat := 118140960795 + 5307469 * 2 ^ 59
def prefixEnd_5307469 : Nat := 4983230072969 + 3 ^ 40 * 5307469 * 2
def baseEnd_5307469 : Nat := 2725282655837800236828901

theorem tailTrace_5307469 : CollatzResearch.WordTrace tailWord_5307469 prefixEnd_5307469 2725282655837800236828901 := by
  unfold tailWord_5307469
  simp only [CollatzResearch.WordTrace]
  refine ⟨193579297608953731384653461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129052865072635820923102307 193579297608953731384653461)
  ·
    refine ⟨9074029575419706158655631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 193579297608953731384653461 9074029575419706158655631)
    ·
      refine ⟨13611044363129559237983447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9074029575419706158655631 13611044363129559237983447)
      ·
        refine ⟨20416566544694338856975171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13611044363129559237983447 20416566544694338856975171)
        ·
          refine ⟨30624849817041508285462757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20416566544694338856975171 30624849817041508285462757)
          ·
            refine ⟨5742159340695282803524267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30624849817041508285462757 5742159340695282803524267)
            ·
              refine ⟨8613239011042924205286401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5742159340695282803524267 8613239011042924205286401)
              ·
                refine ⟨6459929258282193153964801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8613239011042924205286401 6459929258282193153964801)
                ·
                  refine ⟨4844946943711644865473601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6459929258282193153964801 4844946943711644865473601)
                  ·
                    refine ⟨3633710207783733649105201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4844946943711644865473601 3633710207783733649105201)
                    ·
                      refine ⟨2725282655837800236828901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3633710207783733649105201 2725282655837800236828901)
                      ·
                        rfl

theorem cell23_5307469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_5307469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307469 prefixEnd_5307469 := by exact prefixLift 5307469
  have htrace : WordTrace (prefixWord ++ tailWord_5307469) baseStart_5307469 baseEnd_5307469 := by
    simpa [prefixWord, tailWord_5307469, baseEnd_5307469] using wordTrace_append hprefix tailTrace_5307469
  have hstable : (prefixWord ++ tailWord_5307469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307469).length < 2 ^ (prefixWord ++ tailWord_5307469).sum := by decide
  have hdescent : baseEnd_5307469 < baseStart_5307469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307509 : List Nat := [1, 3, 4, 3, 2, 1, 1, 3, 5]
def baseStart_5307509 : Nat := 118140960795 + 5307509 * 2 ^ 59
def prefixEnd_5307509 : Nat := 4983230072969 + 3 ^ 40 * 5307509 * 2
def baseEnd_5307509 : Nat := 302811466118220008925413

theorem tailTrace_5307509 : CollatzResearch.WordTrace tailWord_5307509 prefixEnd_5307509 302811466118220008925413 := by
  unfold tailWord_5307509
  simp only [CollatzResearch.WordTrace]
  refine ⟨193580756528808818216109581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129053837685872545477406387 193580756528808818216109581)
  ·
    refine ⟨72592783698303306831041093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193580756528808818216109581 72592783698303306831041093)
    ·
      refine ⟨13611146943431870030820205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72592783698303306831041093 13611146943431870030820205)
      ·
        refine ⟨5104180103786951261557577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13611146943431870030820205 5104180103786951261557577)
        ·
          refine ⟨3828135077840213446168183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5104180103786951261557577 3828135077840213446168183)
          ·
            refine ⟨5742202616760320169252275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3828135077840213446168183 5742202616760320169252275)
            ·
              refine ⟨8613303925140480253878413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5742202616760320169252275 8613303925140480253878413)
              ·
                refine ⟨3229988971927680095204405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8613303925140480253878413 3229988971927680095204405)
                ·
                  refine ⟨302811466118220008925413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3229988971927680095204405 302811466118220008925413)
                  ·
                    rfl

theorem cell23_5307509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 3, 5].length) (baseStart_5307509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307509 prefixEnd_5307509 := by exact prefixLift 5307509
  have htrace : WordTrace (prefixWord ++ tailWord_5307509) baseStart_5307509 baseEnd_5307509 := by
    simpa [prefixWord, tailWord_5307509, baseEnd_5307509] using wordTrace_append hprefix tailTrace_5307509
  have hstable : (prefixWord ++ tailWord_5307509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307509).length < 2 ^ (prefixWord ++ tailWord_5307509).sum := by decide
  have hdescent : baseEnd_5307509 < baseStart_5307509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307511 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 3]
def baseStart_5307511 : Nat := 118140960795 + 5307511 * 2 ^ 59
def prefixEnd_5307511 : Nat := 4983230072969 + 3 ^ 40 * 5307511 * 2
def baseEnd_5307511 : Nat := 2725304222025289072503707

theorem tailTrace_5307511 : CollatzResearch.WordTrace tailWord_5307511 prefixEnd_5307511 2725304222025289072503707 := by
  unfold tailWord_5307511
  simp only [CollatzResearch.WordTrace]
  refine ⟨193580829474801572557682387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129053886316534381705121591 193580829474801572557682387)
  ·
    refine ⟨290371244212202358836523581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193580829474801572557682387 290371244212202358836523581)
    ·
      refine ⟨108889216579575884563696343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290371244212202358836523581 108889216579575884563696343)
      ·
        refine ⟨163333824869363826845544515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108889216579575884563696343 163333824869363826845544515)
        ·
          refine ⟨245000737304045740268316773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163333824869363826845544515 245000737304045740268316773)
          ·
            refine ⟨45937638244508576300309395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245000737304045740268316773 45937638244508576300309395)
            ·
              refine ⟨68906457366762864450464093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45937638244508576300309395 68906457366762864450464093)
              ·
                refine ⟨25839921512536074168924035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68906457366762864450464093 25839921512536074168924035)
                ·
                  refine ⟨38759882268804111253386053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25839921512536074168924035 38759882268804111253386053)
                  ·
                    refine ⟨7267477925400770860009885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38759882268804111253386053 7267477925400770860009885)
                    ·
                      refine ⟨2725304222025289072503707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7267477925400770860009885 2725304222025289072503707)
                      ·
                        rfl

theorem cell23_5307511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_5307511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307511 prefixEnd_5307511 := by exact prefixLift 5307511
  have htrace : WordTrace (prefixWord ++ tailWord_5307511) baseStart_5307511 baseEnd_5307511 := by
    simpa [prefixWord, tailWord_5307511, baseEnd_5307511] using wordTrace_append hprefix tailTrace_5307511
  have hstable : (prefixWord ++ tailWord_5307511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307511).length < 2 ^ (prefixWord ++ tailWord_5307511).sum := by decide
  have hdescent : baseEnd_5307511 < baseStart_5307511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307541 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 2, 5, 3]
def baseStart_5307541 : Nat := 118140960795 + 5307541 * 2 ^ 59
def prefixEnd_5307541 : Nat := 4983230072969 + 3 ^ 40 * 5307541 * 2
def baseEnd_5307541 : Nat := 2725319626444923955128569

theorem tailTrace_5307541 : CollatzResearch.WordTrace tailWord_5307541 prefixEnd_5307541 2725319626444923955128569 := by
  unfold tailWord_5307541
  simp only [CollatzResearch.WordTrace]
  refine ⟨193581923664692887681274477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129054615776461925120849651 193581923664692887681274477)
  ·
    refine ⟨72593221374259832880477929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193581923664692887681274477 72593221374259832880477929)
    ·
      refine ⟨54444916030694874660358447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72593221374259832880477929 54444916030694874660358447)
      ·
        refine ⟨81667374046042311990537671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54444916030694874660358447 81667374046042311990537671)
        ·
          refine ⟨122501061069063467985806507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81667374046042311990537671 122501061069063467985806507)
          ·
            refine ⟨183751591603595201978709761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122501061069063467985806507 183751591603595201978709761)
            ·
              refine ⟨137813693702696401484032321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183751591603595201978709761 137813693702696401484032321)
              ·
                refine ⟨103360270277022301113024241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137813693702696401484032321 103360270277022301113024241)
                ·
                  refine ⟨77520202707766725834768181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103360270277022301113024241 77520202707766725834768181)
                  ·
                    refine ⟨7267519003853130547009517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77520202707766725834768181 7267519003853130547009517)
                    ·
                      refine ⟨2725319626444923955128569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7267519003853130547009517 2725319626444923955128569)
                      ·
                        rfl

theorem cell23_5307541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_5307541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307541 prefixEnd_5307541 := by exact prefixLift 5307541
  have htrace : WordTrace (prefixWord ++ tailWord_5307541) baseStart_5307541 baseEnd_5307541 := by
    simpa [prefixWord, tailWord_5307541, baseEnd_5307541] using wordTrace_append hprefix tailTrace_5307541
  have hstable : (prefixWord ++ tailWord_5307541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307541).length < 2 ^ (prefixWord ++ tailWord_5307541).sum := by decide
  have hdescent : baseEnd_5307541 < baseStart_5307541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307548 : List Nat := [2, 2, 3, 2, 1, 3, 1, 3, 6]
def baseStart_5307548 : Nat := 118140960795 + 5307548 * 2 ^ 59
def prefixEnd_5307548 : Nat := 4983230072969 + 3 ^ 40 * 5307548 * 2
def baseEnd_5307548 : Nat := 302813691201056158637893

theorem tailTrace_5307548 : CollatzResearch.WordTrace tailWord_5307548 prefixEnd_5307548 302813691201056158637893 := by
  unfold tailWord_5307548
  simp only [CollatzResearch.WordTrace]
  refine ⟨96791089487833763938389649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129054785983778351917852865 96791089487833763938389649)
  ·
    refine ⟨72593317115875322953792237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96791089487833763938389649 72593317115875322953792237)
    ·
      refine ⟨27222493918453246107672089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72593317115875322953792237 27222493918453246107672089)
      ·
        refine ⟨20416870438839934580754067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27222493918453246107672089 20416870438839934580754067)
        ·
          refine ⟨30625305658259901871131101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20416870438839934580754067 30625305658259901871131101)
          ·
            refine ⟨11484489621847463201674163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30625305658259901871131101 11484489621847463201674163)
            ·
              refine ⟨17226734432771194802511245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11484489621847463201674163 17226734432771194802511245)
              ·
                refine ⟨6460025412289198050941717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17226734432771194802511245 6460025412289198050941717)
                ·
                  refine ⟨302813691201056158637893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6460025412289198050941717 302813691201056158637893)
                  ·
                    rfl

theorem cell23_5307548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 3, 6].length) (baseStart_5307548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307548 prefixEnd_5307548 := by exact prefixLift 5307548
  have htrace : WordTrace (prefixWord ++ tailWord_5307548) baseStart_5307548 baseEnd_5307548 := by
    simpa [prefixWord, tailWord_5307548, baseEnd_5307548] using wordTrace_append hprefix tailTrace_5307548
  have hstable : (prefixWord ++ tailWord_5307548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307548).length < 2 ^ (prefixWord ++ tailWord_5307548).sum := by decide
  have hdescent : baseEnd_5307548 < baseStart_5307548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307562 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_5307562 : Nat := 118140960795 + 5307562 * 2 ^ 59
def prefixEnd_5307562 : Nat := 4983230072969 + 3 ^ 40 * 5307562 * 2
def baseEnd_5307562 : Nat := 2725330409538668372965973

theorem tailTrace_5307562 : CollatzResearch.WordTrace tailWord_5307562 prefixEnd_5307562 2725330409538668372965973 := by
  unfold tailWord_5307562
  simp only [CollatzResearch.WordTrace]
  refine ⟨48395672399404202066947235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129055126398411205511859293 48395672399404202066947235)
  ·
    refine ⟨72593508599106303100420853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48395672399404202066947235 72593508599106303100420853)
    ·
      refine ⟨6805641431166215915664455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72593508599106303100420853 6805641431166215915664455)
      ·
        refine ⟨10208462146749323873496683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6805641431166215915664455 10208462146749323873496683)
        ·
          refine ⟨15312693220123985810245025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10208462146749323873496683 15312693220123985810245025)
          ·
            refine ⟨11484519915092989357683769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15312693220123985810245025 11484519915092989357683769)
            ·
              refine ⟨8613389936319742018262827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11484519915092989357683769 8613389936319742018262827)
              ·
                refine ⟨12920084904479613027394241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8613389936319742018262827 12920084904479613027394241)
                ·
                  refine ⟨9690063678359709770545681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12920084904479613027394241 9690063678359709770545681)
                  ·
                    refine ⟨7267547758769782327909261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9690063678359709770545681 7267547758769782327909261)
                    ·
                      refine ⟨2725330409538668372965973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7267547758769782327909261 2725330409538668372965973)
                      ·
                        rfl

theorem cell23_5307562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_5307562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307562 prefixEnd_5307562 := by exact prefixLift 5307562
  have htrace : WordTrace (prefixWord ++ tailWord_5307562) baseStart_5307562 baseEnd_5307562 := by
    simpa [prefixWord, tailWord_5307562, baseEnd_5307562] using wordTrace_append hprefix tailTrace_5307562
  have hstable : (prefixWord ++ tailWord_5307562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307562).length < 2 ^ (prefixWord ++ tailWord_5307562).sum := by decide
  have hdescent : baseEnd_5307562 < baseStart_5307562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307568 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 6, 3, 2]
def baseStart_5307568 : Nat := 118140960795 + 5307568 * 2 ^ 59
def prefixEnd_5307568 : Nat := 4983230072969 + 3 ^ 40 * 5307568 * 2
def baseEnd_5307568 : Nat := 2725333490422595349490945

theorem tailTrace_5307568 : CollatzResearch.WordTrace tailWord_5307568 prefixEnd_5307568 2725333490422595349490945 := by
  unfold tailWord_5307568
  simp only [CollatzResearch.WordTrace]
  refine ⟨96791454217797535646253679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129055272290396714195004905 96791454217797535646253679)
  ·
    refine ⟨145187181326696303469380519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96791454217797535646253679 145187181326696303469380519)
    ·
      refine ⟨217780771990044455204070779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145187181326696303469380519 217780771990044455204070779)
      ·
        refine ⟨326671157985066682806106169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217780771990044455204070779 326671157985066682806106169)
        ·
          refine ⟨245003368488800012104579627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326671157985066682806106169 245003368488800012104579627)
          ·
            refine ⟨367505052733200018156869441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245003368488800012104579627 367505052733200018156869441)
            ·
              refine ⟨275628789549900013617652081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367505052733200018156869441 275628789549900013617652081)
              ·
                refine ⟨206721592162425010213239061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275628789549900013617652081 206721592162425010213239061)
                ·
                  refine ⟨9690074632613672353745581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 206721592162425010213239061 9690074632613672353745581)
                  ·
                    refine ⟨3633777987230127132654593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9690074632613672353745581 3633777987230127132654593)
                    ·
                      refine ⟨2725333490422595349490945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3633777987230127132654593 2725333490422595349490945)
                      ·
                        rfl

theorem cell23_5307568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 6, 3, 2].length) (baseStart_5307568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307568 prefixEnd_5307568 := by exact prefixLift 5307568
  have htrace : WordTrace (prefixWord ++ tailWord_5307568) baseStart_5307568 baseEnd_5307568 := by
    simpa [prefixWord, tailWord_5307568, baseEnd_5307568] using wordTrace_append hprefix tailTrace_5307568
  have hstable : (prefixWord ++ tailWord_5307568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307568).length < 2 ^ (prefixWord ++ tailWord_5307568).sum := by decide
  have hdescent : baseEnd_5307568 < baseStart_5307568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307586 : List Nat := [3, 5, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_5307586 : Nat := 118140960795 + 5307586 * 2 ^ 59
def prefixEnd_5307586 : Nat := 4983230072969 + 3 ^ 40 * 5307586 * 2
def baseEnd_5307586 : Nat := 908447577691458759688621

theorem tailTrace_5307586 : CollatzResearch.WordTrace tailWord_5307586 prefixEnd_5307586 908447577691458759688621 := by
  unfold tailWord_5307586
  simp only [CollatzResearch.WordTrace]
  refine ⟨48395891237382465091665653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129055709966353240244441741 48395891237382465091665653)
  ·
    refine ⟨4537114803504606102343655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48395891237382465091665653 4537114803504606102343655)
    ·
      refine ⟨6805672205256909153515483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4537114803504606102343655 6805672205256909153515483)
      ·
        refine ⟨10208508307885363730273225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6805672205256909153515483 10208508307885363730273225)
        ·
          refine ⟨7656381230914022797704919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10208508307885363730273225 7656381230914022797704919)
          ·
            refine ⟨11484571846371034196557379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7656381230914022797704919 11484571846371034196557379)
            ·
              refine ⟨17226857769556551294836069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11484571846371034196557379 17226857769556551294836069)
              ·
                refine ⟨3230035831791853367781763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17226857769556551294836069 3230035831791853367781763)
                ·
                  refine ⟨4845053747687780051672645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3230035831791853367781763 4845053747687780051672645)
                  ·
                    refine ⟨908447577691458759688621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4845053747687780051672645 908447577691458759688621)
                    ·
                      rfl

theorem cell23_5307586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_5307586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307586 prefixEnd_5307586 := by exact prefixLift 5307586
  have htrace : WordTrace (prefixWord ++ tailWord_5307586) baseStart_5307586 baseEnd_5307586 := by
    simpa [prefixWord, tailWord_5307586, baseEnd_5307586] using wordTrace_append hprefix tailTrace_5307586
  have hstable : (prefixWord ++ tailWord_5307586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307586).length < 2 ^ (prefixWord ++ tailWord_5307586).sum := by decide
  have hdescent : baseEnd_5307586 < baseStart_5307586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307601 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 3, 1, 5]
def baseStart_5307601 : Nat := 118140960795 + 5307601 * 2 ^ 59
def prefixEnd_5307601 : Nat := 4983230072969 + 3 ^ 40 * 5307601 * 2
def baseEnd_5307601 : Nat := 2725350435284193720378293

theorem tailTrace_5307601 : CollatzResearch.WordTrace tailWord_5307601 prefixEnd_5307601 2725350435284193720378293 := by
  unfold tailWord_5307601
  simp only [CollatzResearch.WordTrace]
  refine ⟨193584112044475517928458657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129056074696317011952305771 193584112044475517928458657)
  ·
    refine ⟨145188084033356638446343993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193584112044475517928458657 145188084033356638446343993)
    ·
      refine ⟨108891063025017478834757995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145188084033356638446343993 108891063025017478834757995)
      ·
        refine ⟨163336594537526218252136993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108891063025017478834757995 163336594537526218252136993)
        ·
          refine ⟨122502445903144663689102745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163336594537526218252136993 122502445903144663689102745)
          ·
            refine ⟨91876834427358497766827059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122502445903144663689102745 91876834427358497766827059)
            ·
              refine ⟨137815251641037746650240589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91876834427358497766827059 137815251641037746650240589)
              ·
                refine ⟨51680719365389154993840221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137815251641037746650240589 51680719365389154993840221)
                ·
                  refine ⟨19380269762020933122690083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51680719365389154993840221 19380269762020933122690083)
                  ·
                    refine ⟨29070404643031399684035125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19380269762020933122690083 29070404643031399684035125)
                    ·
                      refine ⟨2725350435284193720378293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29070404643031399684035125 2725350435284193720378293)
                      ·
                        rfl

theorem cell23_5307601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_5307601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307601 prefixEnd_5307601 := by exact prefixLift 5307601
  have htrace : WordTrace (prefixWord ++ tailWord_5307601) baseStart_5307601 baseEnd_5307601 := by
    simpa [prefixWord, tailWord_5307601, baseEnd_5307601] using wordTrace_append hprefix tailTrace_5307601
  have hstable : (prefixWord ++ tailWord_5307601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307601).length < 2 ^ (prefixWord ++ tailWord_5307601).sum := by decide
  have hdescent : baseEnd_5307601 < baseStart_5307601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307615 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 5, 2, 2]
def baseStart_5307615 : Nat := 118140960795 + 5307615 * 2 ^ 59
def prefixEnd_5307615 : Nat := 4983230072969 + 3 ^ 40 * 5307615 * 2
def baseEnd_5307615 : Nat := 2725357624013356665603229

theorem tailTrace_5307615 : CollatzResearch.WordTrace tailWord_5307615 prefixEnd_5307615 2725357624013356665603229 := by
  unfold tailWord_5307615
  simp only [CollatzResearch.WordTrace]
  refine ⟨193584622666424798319468299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129056415110949865546312199 193584622666424798319468299)
  ·
    refine ⟨290376933999637197479202449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193584622666424798319468299 290376933999637197479202449)
    ·
      refine ⟨217782700499727898109401837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290376933999637197479202449 217782700499727898109401837)
      ·
        refine ⟨81668512687397961791025689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217782700499727898109401837 81668512687397961791025689)
        ·
          refine ⟨61251384515548471343269267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81668512687397961791025689 61251384515548471343269267)
          ·
            refine ⟨91877076773322707014903901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61251384515548471343269267 91877076773322707014903901)
            ·
              refine ⟨34453903789996015130588963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91877076773322707014903901 34453903789996015130588963)
              ·
                refine ⟨51680855684994022695883445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34453903789996015130588963 51680855684994022695883445)
                ·
                  refine ⟨4845080220468189627739073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51680855684994022695883445 4845080220468189627739073)
                  ·
                    refine ⟨3633810165351142220804305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4845080220468189627739073 3633810165351142220804305)
                    ·
                      refine ⟨2725357624013356665603229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3633810165351142220804305 2725357624013356665603229)
                      ·
                        rfl

theorem cell23_5307615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_5307615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307615 prefixEnd_5307615 := by exact prefixLift 5307615
  have htrace : WordTrace (prefixWord ++ tailWord_5307615) baseStart_5307615 baseEnd_5307615 := by
    simpa [prefixWord, tailWord_5307615, baseEnd_5307615] using wordTrace_append hprefix tailTrace_5307615
  have hstable : (prefixWord ++ tailWord_5307615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307615).length < 2 ^ (prefixWord ++ tailWord_5307615).sum := by decide
  have hdescent : baseEnd_5307615 < baseStart_5307615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307628 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 4]
def baseStart_5307628 : Nat := 118140960795 + 5307628 * 2 ^ 59
def prefixEnd_5307628 : Nat := 4983230072969 + 3 ^ 40 * 5307628 * 2
def baseEnd_5307628 : Nat := 2725364299261865114740669

theorem tailTrace_5307628 : CollatzResearch.WordTrace tailWord_5307628 prefixEnd_5307628 2725364299261865114740669 := by
  unfold tailWord_5307628
  simp only [CollatzResearch.WordTrace]
  refine ⟨96792548407688850769845769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129056731210251801026461025 96792548407688850769845769)
  ·
    refine ⟨72594411305766638077384327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96792548407688850769845769 72594411305766638077384327)
    ·
      refine ⟨108891616958649957116076491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72594411305766638077384327 108891616958649957116076491)
      ·
        refine ⟨163337425437974935674114737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108891616958649957116076491 163337425437974935674114737)
        ·
          refine ⟨122503069078481201755586053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163337425437974935674114737 122503069078481201755586053)
          ·
            refine ⟨22969325452215225329172385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122503069078481201755586053 22969325452215225329172385)
            ·
              refine ⟨17226994089161418996879289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22969325452215225329172385 17226994089161418996879289)
              ·
                refine ⟨12920245566871064247659467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17226994089161418996879289 12920245566871064247659467)
                ·
                  refine ⟨19380368350306596371489201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12920245566871064247659467 19380368350306596371489201)
                  ·
                    refine ⟨14535276262729947278616901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19380368350306596371489201 14535276262729947278616901)
                    ·
                      refine ⟨2725364299261865114740669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14535276262729947278616901 2725364299261865114740669)
                      ·
                        rfl

theorem cell23_5307628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_5307628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307628 prefixEnd_5307628 := by exact prefixLift 5307628
  have htrace : WordTrace (prefixWord ++ tailWord_5307628) baseStart_5307628 baseEnd_5307628 := by
    simpa [prefixWord, tailWord_5307628, baseEnd_5307628] using wordTrace_append hprefix tailTrace_5307628
  have hstable : (prefixWord ++ tailWord_5307628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307628).length < 2 ^ (prefixWord ++ tailWord_5307628).sum := by decide
  have hdescent : baseEnd_5307628 < baseStart_5307628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307635 : List Nat := [1, 1, 1, 2, 2, 6, 1, 3, 1, 2, 3]
def baseStart_5307635 : Nat := 118140960795 + 5307635 * 2 ^ 59
def prefixEnd_5307635 : Nat := 4983230072969 + 3 ^ 40 * 5307635 * 2
def baseEnd_5307635 : Nat := 2725367893626446587353137

theorem tailTrace_5307635 : CollatzResearch.WordTrace tailWord_5307635 prefixEnd_5307635 2725367893626446587353137 := by
  unfold tailWord_5307635
  simp only [CollatzResearch.WordTrace]
  refine ⟨193585352126352341735196359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129056901417568227823464239 193585352126352341735196359)
  ·
    refine ⟨290378028189528512602794539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193585352126352341735196359 290378028189528512602794539)
    ·
      refine ⟨435567042284292768904191809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290378028189528512602794539 435567042284292768904191809)
      ·
        refine ⟨326675281713219576678143857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435567042284292768904191809 326675281713219576678143857)
        ·
          refine ⟨245006461284914682508607893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326675281713219576678143857 245006461284914682508607893)
          ·
            refine ⟨11484677872730375742590995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 245006461284914682508607893 11484677872730375742590995)
            ·
              refine ⟨17227016809095563613886493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11484677872730375742590995 17227016809095563613886493)
              ·
                refine ⟨6460131303410836355207435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17227016809095563613886493 6460131303410836355207435)
                ·
                  refine ⟨9690196955116254532811153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6460131303410836355207435 9690196955116254532811153)
                  ·
                    refine ⟨7267647716337190899608365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9690196955116254532811153 7267647716337190899608365)
                    ·
                      refine ⟨2725367893626446587353137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7267647716337190899608365 2725367893626446587353137)
                      ·
                        rfl

theorem cell23_5307635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 2, 3].length) (baseStart_5307635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307635 prefixEnd_5307635 := by exact prefixLift 5307635
  have htrace : WordTrace (prefixWord ++ tailWord_5307635) baseStart_5307635 baseEnd_5307635 := by
    simpa [prefixWord, tailWord_5307635, baseEnd_5307635] using wordTrace_append hprefix tailTrace_5307635
  have hstable : (prefixWord ++ tailWord_5307635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307635).length < 2 ^ (prefixWord ++ tailWord_5307635).sum := by decide
  have hdescent : baseEnd_5307635 < baseStart_5307635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307649 : List Nat := [1, 2, 4, 1, 1, 3, 2, 4, 1, 2, 2]
def baseStart_5307649 : Nat := 118140960795 + 5307649 * 2 ^ 59
def prefixEnd_5307649 : Nat := 4983230072969 + 3 ^ 40 * 5307649 * 2
def baseEnd_5307649 : Nat := 2725375082355609532578073

theorem tailTrace_5307649 : CollatzResearch.WordTrace tailWord_5307649 prefixEnd_5307649 2725375082355609532578073 := by
  unfold tailWord_5307649
  simp only [CollatzResearch.WordTrace]
  refine ⟨193585862748301622126206001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129057241832201081417470667 193585862748301622126206001)
  ·
    refine ⟨145189397061226216594654501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193585862748301622126206001 145189397061226216594654501)
    ·
      refine ⟨27223011948979915611497719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145189397061226216594654501 27223011948979915611497719)
      ·
        refine ⟨40834517923469873417246579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27223011948979915611497719 40834517923469873417246579)
        ·
          refine ⟨61251776885204810125869869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40834517923469873417246579 61251776885204810125869869)
          ·
            refine ⟨22969416331951803797201201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61251776885204810125869869 22969416331951803797201201)
            ·
              refine ⟨17227062248963852847900901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22969416331951803797201201 17227062248963852847900901)
              ·
                refine ⟨3230074171680722408981419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17227062248963852847900901 3230074171680722408981419)
                ·
                  refine ⟨4845111257521083613472129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3230074171680722408981419 4845111257521083613472129)
                  ·
                    refine ⟨3633833443140812710104097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4845111257521083613472129 3633833443140812710104097)
                    ·
                      refine ⟨2725375082355609532578073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3633833443140812710104097 2725375082355609532578073)
                      ·
                        rfl

theorem cell23_5307649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_5307649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307649 prefixEnd_5307649 := by exact prefixLift 5307649
  have htrace : WordTrace (prefixWord ++ tailWord_5307649) baseStart_5307649 baseEnd_5307649 := by
    simpa [prefixWord, tailWord_5307649, baseEnd_5307649] using wordTrace_append hprefix tailTrace_5307649
  have hstable : (prefixWord ++ tailWord_5307649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307649).length < 2 ^ (prefixWord ++ tailWord_5307649).sum := by decide
  have hdescent : baseEnd_5307649 < baseStart_5307649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307716 : List Nat := [2, 3, 4, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_5307716 : Nat := 118140960795 + 5307716 * 2 ^ 59
def prefixEnd_5307716 : Nat := 4983230072969 + 3 ^ 40 * 5307716 * 2
def baseEnd_5307716 : Nat := 2725409485559460770440265

theorem tailTrace_5307716 : CollatzResearch.WordTrace tailWord_5307716 prefixEnd_5307716 2725409485559460770440265 := by
  unfold tailWord_5307716
  simp only [CollatzResearch.WordTrace]
  refine ⟨96794153219529446284447501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129058870959372595045930001 96794153219529446284447501)
  ·
    refine ⟨36297807457323542356667813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96794153219529446284447501 36297807457323542356667813)
    ·
      refine ⟨6805838898248164191875215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36297807457323542356667813 6805838898248164191875215)
      ·
        refine ⟨10208758347372246287812823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6805838898248164191875215 10208758347372246287812823)
        ·
          refine ⟨15313137521058369431719235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10208758347372246287812823 15313137521058369431719235)
          ·
            refine ⟨22969706281587554147578853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15313137521058369431719235 22969706281587554147578853)
            ·
              refine ⟨4306819927797666402671035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22969706281587554147578853 4306819927797666402671035)
              ·
                refine ⟨6460229891696499604006553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4306819927797666402671035 6460229891696499604006553)
                ·
                  refine ⟨4845172418772374703004915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6460229891696499604006553 4845172418772374703004915)
                  ·
                    refine ⟨7267758628158562054507373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4845172418772374703004915 7267758628158562054507373)
                    ·
                      refine ⟨2725409485559460770440265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7267758628158562054507373 2725409485559460770440265)
                      ·
                        rfl

theorem cell23_5307716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_5307716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307716 prefixEnd_5307716 := by exact prefixLift 5307716
  have htrace : WordTrace (prefixWord ++ tailWord_5307716) baseStart_5307716 baseEnd_5307716 := by
    simpa [prefixWord, tailWord_5307716, baseEnd_5307716] using wordTrace_append hprefix tailTrace_5307716
  have hstable : (prefixWord ++ tailWord_5307716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307716).length < 2 ^ (prefixWord ++ tailWord_5307716).sum := by decide
  have hdescent : baseEnd_5307716 < baseStart_5307716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307808 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 6]
def baseStart_5307808 : Nat := 118140960795 + 5307808 * 2 ^ 59
def prefixEnd_5307808 : Nat := 4983230072969 + 3 ^ 40 * 5307808 * 2
def baseEnd_5307808 : Nat := 2725456725779674410489841

theorem tailTrace_5307808 : CollatzResearch.WordTrace tailWord_5307808 prefixEnd_5307808 2725456725779674410489841 := by
  unfold tailWord_5307808
  simp only [CollatzResearch.WordTrace]
  refine ⟨96795830977362796140622039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129061107969817061520829385 96795830977362796140622039)
  ·
    refine ⟨145193746466044194210933059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96795830977362796140622039 145193746466044194210933059)
    ·
      refine ⟨217790619699066291316399589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145193746466044194210933059 217790619699066291316399589)
      ·
        refine ⟨40835741193574929621824923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217790619699066291316399589 40835741193574929621824923)
        ·
          refine ⟨61253611790362394432737385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40835741193574929621824923 61253611790362394432737385)
          ·
            refine ⟨45940208842771795824553039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61253611790362394432737385 45940208842771795824553039)
            ·
              refine ⟨68910313264157693736829559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45940208842771795824553039 68910313264157693736829559)
              ·
                refine ⟨103365469896236540605244339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68910313264157693736829559 103365469896236540605244339)
                ·
                  refine ⟨155048204844354810907866509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103365469896236540605244339 155048204844354810907866509)
                  ·
                    refine ⟨58143076816633054090449941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155048204844354810907866509 58143076816633054090449941)
                    ·
                      refine ⟨2725456725779674410489841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58143076816633054090449941 2725456725779674410489841)
                      ·
                        rfl

theorem cell23_5307808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_5307808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307808 prefixEnd_5307808 := by exact prefixLift 5307808
  have htrace : WordTrace (prefixWord ++ tailWord_5307808) baseStart_5307808 baseEnd_5307808 := by
    simpa [prefixWord, tailWord_5307808, baseEnd_5307808] using wordTrace_append hprefix tailTrace_5307808
  have hstable : (prefixWord ++ tailWord_5307808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307808).length < 2 ^ (prefixWord ++ tailWord_5307808).sum := by decide
  have hdescent : baseEnd_5307808 < baseStart_5307808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307879 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 3, 1, 3]
def baseStart_5307879 : Nat := 118140960795 + 5307879 * 2 ^ 59
def prefixEnd_5307879 : Nat := 4983230072969 + 3 ^ 40 * 5307879 * 2
def baseEnd_5307879 : Nat := 2725493182906143632702015

theorem tailTrace_5307879 : CollatzResearch.WordTrace tailWord_5307879 prefixEnd_5307879 2725493182906143632702015 := by
  unfold tailWord_5307879
  simp only [CollatzResearch.WordTrace]
  refine ⟨193594251537468371407078691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129062834358312247604719127 193594251537468371407078691)
  ·
    refine ⟨290391377306202557110618037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193594251537468371407078691 290391377306202557110618037)
    ·
      refine ⟨27224191622456489729120441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 290391377306202557110618037 27224191622456489729120441)
      ·
        refine ⟨20418143716842367296840331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27224191622456489729120441 20418143716842367296840331)
        ·
          refine ⟨30627215575263550945260497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20418143716842367296840331 30627215575263550945260497)
          ·
            refine ⟨22970411681447663208945373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30627215575263550945260497 22970411681447663208945373)
            ·
              refine ⟨8613904380542873703354515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22970411681447663208945373 8613904380542873703354515)
              ·
                refine ⟨12920856570814310555031773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8613904380542873703354515 12920856570814310555031773)
                ·
                  refine ⟨4845321214055366458136915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12920856570814310555031773 4845321214055366458136915)
                  ·
                    refine ⟨7267981821083049687205373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4845321214055366458136915 7267981821083049687205373)
                    ·
                      refine ⟨2725493182906143632702015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7267981821083049687205373 2725493182906143632702015)
                      ·
                        rfl

theorem cell23_5307879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_5307879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307879 prefixEnd_5307879 := by exact prefixLift 5307879
  have htrace : WordTrace (prefixWord ++ tailWord_5307879) baseStart_5307879 baseEnd_5307879 := by
    simpa [prefixWord, tailWord_5307879, baseEnd_5307879] using wordTrace_append hprefix tailTrace_5307879
  have hstable : (prefixWord ++ tailWord_5307879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307879).length < 2 ^ (prefixWord ++ tailWord_5307879).sum := by decide
  have hdescent : baseEnd_5307879 < baseStart_5307879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307895 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 6, 4]
def baseStart_5307895 : Nat := 118140960795 + 5307895 * 2 ^ 59
def prefixEnd_5307895 : Nat := 4983230072969 + 3 ^ 40 * 5307895 * 2
def baseEnd_5307895 : Nat := 908500466198871856700647

theorem tailTrace_5307895 : CollatzResearch.WordTrace tailWord_5307895 prefixEnd_5307895 908500466198871856700647 := by
  unfold tailWord_5307895
  simp only [CollatzResearch.WordTrace]
  refine ⟨193594835105410406139661139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129063223403606937426440759 193594835105410406139661139)
  ·
    refine ⟨290392252658115609209491709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193594835105410406139661139 290392252658115609209491709)
    ·
      refine ⟨108897094746793353453559391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290392252658115609209491709 108897094746793353453559391)
      ·
        refine ⟨163345642120190030180339087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108897094746793353453559391 163345642120190030180339087)
        ·
          refine ⟨245018463180285045270508631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163345642120190030180339087 245018463180285045270508631)
          ·
            refine ⟨367527694770427567905762947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245018463180285045270508631 367527694770427567905762947)
            ·
              refine ⟨551291542155641351858644421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367527694770427567905762947 551291542155641351858644421)
              ·
                refine ⟨103367164154182753473495829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 551291542155641351858644421 103367164154182753473495829)
                ·
                  refine ⟨4845335819727316569070117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103367164154182753473495829 4845335819727316569070117)
                  ·
                    refine ⟨908500466198871856700647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4845335819727316569070117 908500466198871856700647)
                    ·
                      rfl

theorem cell23_5307895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 4].length) (baseStart_5307895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307895 prefixEnd_5307895 := by exact prefixLift 5307895
  have htrace : WordTrace (prefixWord ++ tailWord_5307895) baseStart_5307895 baseEnd_5307895 := by
    simpa [prefixWord, tailWord_5307895, baseEnd_5307895] using wordTrace_append hprefix tailTrace_5307895
  have hstable : (prefixWord ++ tailWord_5307895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307895).length < 2 ^ (prefixWord ++ tailWord_5307895).sum := by decide
  have hdescent : baseEnd_5307895 < baseStart_5307895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307906 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_5307906 : Nat := 118140960795 + 5307906 * 2 ^ 59
def prefixEnd_5307906 : Nat := 4983230072969 + 3 ^ 40 * 5307906 * 2
def baseEnd_5307906 : Nat := 2725507046883815027064391

theorem tailTrace_5307906 : CollatzResearch.WordTrace tailWord_5307906 prefixEnd_5307906 2725507046883815027064391 := by
  unfold tailWord_5307906
  simp only [CollatzResearch.WordTrace]
  refine ⟨48398809077092638754577893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129063490872247036678874381 48398809077092638754577893)
  ·
    refine ⟨9074776701954869766483355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48398809077092638754577893 9074776701954869766483355)
    ·
      refine ⟨13612165052932304649725033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9074776701954869766483355 13612165052932304649725033)
      ·
        refine ⟨10209123789699228487293775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13612165052932304649725033 10209123789699228487293775)
        ·
          refine ⟨15313685684548842730940663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10209123789699228487293775 15313685684548842730940663)
          ·
            refine ⟨22970528526823264096410995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15313685684548842730940663 22970528526823264096410995)
            ·
              refine ⟨34455792790234896144616493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22970528526823264096410995 34455792790234896144616493)
              ·
                refine ⟨12920922296338086054231185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34455792790234896144616493 12920922296338086054231185)
                ·
                  refine ⟨9690691722253564540673389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12920922296338086054231185 9690691722253564540673389)
                  ·
                    refine ⟨3634009395845086702752521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9690691722253564540673389 3634009395845086702752521)
                    ·
                      refine ⟨2725507046883815027064391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3634009395845086702752521 2725507046883815027064391)
                      ·
                        rfl

theorem cell23_5307906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_5307906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307906 prefixEnd_5307906 := by exact prefixLift 5307906
  have htrace : WordTrace (prefixWord ++ tailWord_5307906) baseStart_5307906 baseEnd_5307906 := by
    simpa [prefixWord, tailWord_5307906, baseEnd_5307906] using wordTrace_append hprefix tailTrace_5307906
  have hstable : (prefixWord ++ tailWord_5307906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307906).length < 2 ^ (prefixWord ++ tailWord_5307906).sum := by decide
  have hdescent : baseEnd_5307906 < baseStart_5307906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307952 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 6, 1, 3]
def baseStart_5307952 : Nat := 118140960795 + 5307952 * 2 ^ 59
def prefixEnd_5307952 : Nat := 4983230072969 + 3 ^ 40 * 5307952 * 2
def baseEnd_5307952 : Nat := 2725530666993921847089179

theorem tailTrace_5307952 : CollatzResearch.WordTrace tailWord_5307952 prefixEnd_5307952 2725530666993921847089179 := by
  unfold tailWord_5307952
  simp only [CollatzResearch.WordTrace]
  refine ⟨96798457033101952437243055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129064609377469269916324073 96798457033101952437243055)
  ·
    refine ⟨145197685549652928655864583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96798457033101952437243055 145197685549652928655864583)
    ·
      refine ⟨217796528324479392983796875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145197685549652928655864583 217796528324479392983796875)
      ·
        refine ⟨326694792486719089475695313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217796528324479392983796875 326694792486719089475695313)
        ·
          refine ⟨245021094365039317106771485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326694792486719089475695313 245021094365039317106771485)
          ·
            refine ⟨91882910386889743915039307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245021094365039317106771485 91882910386889743915039307)
            ·
              refine ⟨137824365580334615872558961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91882910386889743915039307 137824365580334615872558961)
              ·
                refine ⟨103368274185250961904419221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137824365580334615872558961 103368274185250961904419221)
                ·
                  refine ⟨4845387852433638839269651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103368274185250961904419221 4845387852433638839269651)
                  ·
                    refine ⟨7268081778650458258904477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4845387852433638839269651 7268081778650458258904477)
                    ·
                      refine ⟨2725530666993921847089179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7268081778650458258904477 2725530666993921847089179)
                      ·
                        rfl

theorem cell23_5307952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 6, 1, 3].length) (baseStart_5307952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307952 prefixEnd_5307952 := by exact prefixLift 5307952
  have htrace : WordTrace (prefixWord ++ tailWord_5307952) baseStart_5307952 baseEnd_5307952 := by
    simpa [prefixWord, tailWord_5307952, baseEnd_5307952] using wordTrace_append hprefix tailTrace_5307952
  have hstable : (prefixWord ++ tailWord_5307952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307952).length < 2 ^ (prefixWord ++ tailWord_5307952).sum := by decide
  have hdescent : baseEnd_5307952 < baseStart_5307952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307969 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_5307969 : Nat := 118140960795 + 5307969 * 2 ^ 59
def prefixEnd_5307969 : Nat := 4983230072969 + 3 ^ 40 * 5307969 * 2
def baseEnd_5307969 : Nat := 2725539396165048280576601

theorem tailTrace_5307969 : CollatzResearch.WordTrace tailWord_5307969 prefixEnd_5307969 2725539396165048280576601 := by
  unfold tailWord_5307969
  simp only [CollatzResearch.WordTrace]
  refine ⟨193597534107142316777854961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129065022738094877851903307 193597534107142316777854961)
  ·
    refine ⟨145198150580356737583391221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193597534107142316777854961 145198150580356737583391221)
    ·
      refine ⟨13612326616908444148442927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145198150580356737583391221 13612326616908444148442927)
      ·
        refine ⟨20418489925362666222664391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13612326616908444148442927 20418489925362666222664391)
        ·
          refine ⟨30627734888043999333996587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20418489925362666222664391 30627734888043999333996587)
          ·
            refine ⟨45941602332065999000994881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30627734888043999333996587 45941602332065999000994881)
            ·
              refine ⟨34456201749049499250746161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45941602332065999000994881 34456201749049499250746161)
              ·
                refine ⟨25842151311787124438059621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34456201749049499250746161 25842151311787124438059621)
                ·
                  refine ⟨4845403370960085832136179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25842151311787124438059621 4845403370960085832136179)
                  ·
                    refine ⟨7268105056440128748204269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4845403370960085832136179 7268105056440128748204269)
                    ·
                      refine ⟨2725539396165048280576601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7268105056440128748204269 2725539396165048280576601)
                      ·
                        rfl

theorem cell23_5307969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_5307969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307969 prefixEnd_5307969 := by exact prefixLift 5307969
  have htrace : WordTrace (prefixWord ++ tailWord_5307969) baseStart_5307969 baseEnd_5307969 := by
    simpa [prefixWord, tailWord_5307969, baseEnd_5307969] using wordTrace_append hprefix tailTrace_5307969
  have hstable : (prefixWord ++ tailWord_5307969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307969).length < 2 ^ (prefixWord ++ tailWord_5307969).sum := by decide
  have hdescent : baseEnd_5307969 < baseStart_5307969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307985 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 4, 6]
def baseStart_5307985 : Nat := 118140960795 + 5307985 * 2 ^ 59
def prefixEnd_5307985 : Nat := 4983230072969 + 3 ^ 40 * 5307985 * 2
def baseEnd_5307985 : Nat := 908515870618506739325509

theorem tailTrace_5307985 : CollatzResearch.WordTrace tailWord_5307985 prefixEnd_5307985 908515870618506739325509 := by
  unfold tailWord_5307985
  simp only [CollatzResearch.WordTrace]
  refine ⟨193598117675084351510437409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129065411783389567673624939 193598117675084351510437409)
  ·
    refine ⟨145198588256313263632828057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193598117675084351510437409 145198588256313263632828057)
    ·
      refine ⟨108898941192234947724621043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145198588256313263632828057 108898941192234947724621043)
      ·
        refine ⟨163348411788352421586931565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108898941192234947724621043 163348411788352421586931565)
        ·
          refine ⟨61255654420632158095099337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163348411788352421586931565 61255654420632158095099337)
          ·
            refine ⟨45941740815474118571324503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61255654420632158095099337 45941740815474118571324503)
            ·
              refine ⟨68912611223211177856986755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45941740815474118571324503 68912611223211177856986755)
              ·
                refine ⟨103368916834816766785480133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68912611223211177856986755 103368916834816766785480133)
                ·
                  refine ⟨19381671906528143772277525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103368916834816766785480133 19381671906528143772277525)
                  ·
                    refine ⟨908515870618506739325509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19381671906528143772277525 908515870618506739325509)
                    ·
                      rfl

theorem cell23_5307985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_5307985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307985 prefixEnd_5307985 := by exact prefixLift 5307985
  have htrace : WordTrace (prefixWord ++ tailWord_5307985) baseStart_5307985 baseEnd_5307985 := by
    simpa [prefixWord, tailWord_5307985, baseEnd_5307985] using wordTrace_append hprefix tailTrace_5307985
  have hstable : (prefixWord ++ tailWord_5307985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307985).length < 2 ^ (prefixWord ++ tailWord_5307985).sum := by decide
  have hdescent : baseEnd_5307985 < baseStart_5307985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5307986 : List Nat := [3, 2, 2, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_5307986 : Nat := 118140960795 + 5307986 * 2 ^ 59
def prefixEnd_5307986 : Nat := 4983230072969 + 3 ^ 40 * 5307986 * 2
def baseEnd_5307986 : Nat := 2725548125336174714064023

theorem tailTrace_5307986 : CollatzResearch.WordTrace tailWord_5307986 prefixEnd_5307986 2725548125336174714064023 := by
  unfold tailWord_5307986
  simp only [CollatzResearch.WordTrace]
  refine ⟨48399538537020182170305953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129065436098720485787482541 48399538537020182170305953)
  ·
    refine ⟨36299653902765136627729465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48399538537020182170305953 36299653902765136627729465)
    ·
      refine ⟨27224740427073852470797099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36299653902765136627729465 27224740427073852470797099)
      ·
        refine ⟨40837110640610778706195649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27224740427073852470797099 40837110640610778706195649)
        ·
          refine ⟨30627832980458084029646737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40837110640610778706195649 30627832980458084029646737)
          ·
            refine ⟨22970874735343563022235053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30627832980458084029646737 22970874735343563022235053)
            ·
              refine ⟨8614078025753836133338145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22970874735343563022235053 8614078025753836133338145)
              ·
                refine ⟨6460558519315377100003609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8614078025753836133338145 6460558519315377100003609)
                ·
                  refine ⟨4845418889486532825002707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6460558519315377100003609 4845418889486532825002707)
                  ·
                    refine ⟨7268128334229799237504061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4845418889486532825002707 7268128334229799237504061)
                    ·
                      refine ⟨2725548125336174714064023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7268128334229799237504061 2725548125336174714064023)
                      ·
                        rfl

theorem cell23_5307986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_5307986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5307986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5307986 prefixEnd_5307986 := by exact prefixLift 5307986
  have htrace : WordTrace (prefixWord ++ tailWord_5307986) baseStart_5307986 baseEnd_5307986 := by
    simpa [prefixWord, tailWord_5307986, baseEnd_5307986] using wordTrace_append hprefix tailTrace_5307986
  have hstable : (prefixWord ++ tailWord_5307986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5307986).length < 2 ^ (prefixWord ++ tailWord_5307986).sum := by decide
  have hdescent : baseEnd_5307986 < baseStart_5307986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5307986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308009 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 1, 4, 2]
def baseStart_5308009 : Nat := 118140960795 + 5308009 * 2 ^ 59
def prefixEnd_5308009 : Nat := 4983230072969 + 3 ^ 40 * 5308009 * 2
def baseEnd_5308009 : Nat := 2725559935391228124076417

theorem tailTrace_5308009 : CollatzResearch.WordTrace tailWord_5308009 prefixEnd_5308009 2725559935391228124076417 := by
  unfold tailWord_5308009
  simp only [CollatzResearch.WordTrace]
  refine ⟨193598993026997403609311081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129065995351331602406207387 193598993026997403609311081)
  ·
    refine ⟨145199244770248052706983311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193598993026997403609311081 145199244770248052706983311)
    ·
      refine ⟨217798867155372079060474967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145199244770248052706983311 217798867155372079060474967)
      ·
        refine ⟨326698300733058118590712451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217798867155372079060474967 326698300733058118590712451)
        ·
          refine ⟨490047451099587177886068677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326698300733058118590712451 490047451099587177886068677)
          ·
            refine ⟨91883897081172595853637877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 490047451099587177886068677 91883897081172595853637877)
            ·
              refine ⟨8614115351359930861278551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91883897081172595853637877 8614115351359930861278551)
              ·
                refine ⟨12921173027039896291917827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8614115351359930861278551 12921173027039896291917827)
                ·
                  refine ⟨19381759540559844437876741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12921173027039896291917827 19381759540559844437876741)
                  ·
                    refine ⟨3634079913854970832101889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19381759540559844437876741 3634079913854970832101889)
                    ·
                      refine ⟨2725559935391228124076417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3634079913854970832101889 2725559935391228124076417)
                      ·
                        rfl

theorem cell23_5308009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 4, 2].length) (baseStart_5308009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308009 prefixEnd_5308009 := by exact prefixLift 5308009
  have htrace : WordTrace (prefixWord ++ tailWord_5308009) baseStart_5308009 baseEnd_5308009 := by
    simpa [prefixWord, tailWord_5308009, baseEnd_5308009] using wordTrace_append hprefix tailTrace_5308009
  have hstable : (prefixWord ++ tailWord_5308009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308009).length < 2 ^ (prefixWord ++ tailWord_5308009).sum := by decide
  have hdescent : baseEnd_5308009 < baseStart_5308009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308013 : List Nat := [1, 5, 1, 1, 4, 1, 2, 2, 1, 3, 2]
def baseStart_5308013 : Nat := 118140960795 + 5308013 * 2 ^ 59
def prefixEnd_5308013 : Nat := 4983230072969 + 3 ^ 40 * 5308013 * 2
def baseEnd_5308013 : Nat := 2725561989313846108426399

theorem tailTrace_5308013 : CollatzResearch.WordTrace tailWord_5308013 prefixEnd_5308013 2725561989313846108426399 := by
  unfold tailWord_5308013
  simp only [CollatzResearch.WordTrace]
  refine ⟨193599138918982912292456693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129066092612655274861637795 193599138918982912292456693)
  ·
    refine ⟨18149919273654648027417815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193599138918982912292456693 18149919273654648027417815)
    ·
      refine ⟨27224878910481972041126723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18149919273654648027417815 27224878910481972041126723)
      ·
        refine ⟨40837318365722958061690085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27224878910481972041126723 40837318365722958061690085)
        ·
          refine ⟨7656997193573054636566891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40837318365722958061690085 7656997193573054636566891)
          ·
            refine ⟨11485495790359581954850337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7656997193573054636566891 11485495790359581954850337)
            ·
              refine ⟨8614121842769686466137753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11485495790359581954850337 8614121842769686466137753)
              ·
                refine ⟨6460591382077264849603315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8614121842769686466137753 6460591382077264849603315)
                ·
                  refine ⟨9690887073115897274404973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6460591382077264849603315 9690887073115897274404973)
                  ·
                    refine ⟨3634082652418461477901865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9690887073115897274404973 3634082652418461477901865)
                    ·
                      refine ⟨2725561989313846108426399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3634082652418461477901865 2725561989313846108426399)
                      ·
                        rfl

theorem cell23_5308013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 3, 2].length) (baseStart_5308013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308013 prefixEnd_5308013 := by exact prefixLift 5308013
  have htrace : WordTrace (prefixWord ++ tailWord_5308013) baseStart_5308013 baseEnd_5308013 := by
    simpa [prefixWord, tailWord_5308013, baseEnd_5308013] using wordTrace_append hprefix tailTrace_5308013
  have hstable : (prefixWord ++ tailWord_5308013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308013).length < 2 ^ (prefixWord ++ tailWord_5308013).sum := by decide
  have hdescent : baseEnd_5308013 < baseStart_5308013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308082 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_5308082 : Nat := 118140960795 + 5308082 * 2 ^ 59
def prefixEnd_5308082 : Nat := 4983230072969 + 3 ^ 40 * 5308082 * 2
def baseEnd_5308082 : Nat := 2725597419479006338463581

theorem tailTrace_5308082 : CollatzResearch.WordTrace tailWord_5308082 prefixEnd_5308082 2725597419479006338463581 := by
  unfold tailWord_5308082
  simp only [CollatzResearch.WordTrace]
  refine ⟨48400413888933234269179625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129067770370488624717812333 48400413888933234269179625)
  ·
    refine ⟨36300310416699925701884719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48400413888933234269179625 36300310416699925701884719)
    ·
      refine ⟨54450465625049888552827079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36300310416699925701884719 54450465625049888552827079)
      ·
        refine ⟨81675698437574832829240619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54450465625049888552827079 81675698437574832829240619)
        ·
          refine ⟨122513547656362249243860929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81675698437574832829240619 122513547656362249243860929)
          ·
            refine ⟨91885160742271686932895697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122513547656362249243860929 91885160742271686932895697)
            ·
              refine ⟨68913870556703765199671773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91885160742271686932895697 68913870556703765199671773)
              ·
                refine ⟨25842701458763911949876915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68913870556703765199671773 25842701458763911949876915)
                ·
                  refine ⟨38764052188145867924815373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25842701458763911949876915 38764052188145867924815373)
                  ·
                    refine ⟨14536519570554700471805765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38764052188145867924815373 14536519570554700471805765)
                    ·
                      refine ⟨2725597419479006338463581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14536519570554700471805765 2725597419479006338463581)
                      ·
                        rfl

theorem cell23_5308082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_5308082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308082 prefixEnd_5308082 := by exact prefixLift 5308082
  have htrace : WordTrace (prefixWord ++ tailWord_5308082) baseStart_5308082 baseEnd_5308082 := by
    simpa [prefixWord, tailWord_5308082, baseEnd_5308082] using wordTrace_append hprefix tailTrace_5308082
  have hstable : (prefixWord ++ tailWord_5308082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308082).length < 2 ^ (prefixWord ++ tailWord_5308082).sum := by decide
  have hdescent : baseEnd_5308082 < baseStart_5308082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308116 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 1, 6, 2]
def baseStart_5308116 : Nat := 118140960795 + 5308116 * 2 ^ 59
def prefixEnd_5308116 : Nat := 4983230072969 + 3 ^ 40 * 5308116 * 2
def baseEnd_5308116 : Nat := 2725614877821259205438425

theorem tailTrace_5308116 : CollatzResearch.WordTrace tailWord_5308116 prefixEnd_5308116 2725614877821259205438425 := by
  unfold tailWord_5308116
  simp only [CollatzResearch.WordTrace]
  refine ⟨96801447818804880441728101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129068597091739840588970801 96801447818804880441728101)
  ·
    refine ⟨18150271466025915082824019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96801447818804880441728101 18150271466025915082824019)
    ·
      refine ⟨27225407199038872624236029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18150271466025915082824019 27225407199038872624236029)
      ·
        refine ⟨10209527699639577234088511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27225407199038872624236029 10209527699639577234088511)
        ·
          refine ⟨15314291549459365851132767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10209527699639577234088511 15314291549459365851132767)
          ·
            refine ⟨22971437324189048776699151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15314291549459365851132767 22971437324189048776699151)
            ·
              refine ⟨34457155986283573165048727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22971437324189048776699151 34457155986283573165048727)
              ·
                refine ⟨51685733979425359747573091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34457155986283573165048727 51685733979425359747573091)
                ·
                  refine ⟨77528600969138039621359637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51685733979425359747573091 77528600969138039621359637)
                  ·
                    refine ⟨3634153170428345607251233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77528600969138039621359637 3634153170428345607251233)
                    ·
                      refine ⟨2725614877821259205438425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3634153170428345607251233 2725614877821259205438425)
                      ·
                        rfl

theorem cell23_5308116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_5308116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308116 prefixEnd_5308116 := by exact prefixLift 5308116
  have htrace : WordTrace (prefixWord ++ tailWord_5308116) baseStart_5308116 baseEnd_5308116 := by
    simpa [prefixWord, tailWord_5308116, baseEnd_5308116] using wordTrace_append hprefix tailTrace_5308116
  have hstable : (prefixWord ++ tailWord_5308116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308116).length < 2 ^ (prefixWord ++ tailWord_5308116).sum := by decide
  have hdescent : baseEnd_5308116 < baseStart_5308116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308136 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_5308136 : Nat := 118140960795 + 5308136 * 2 ^ 59
def prefixEnd_5308136 : Nat := 4983230072969 + 3 ^ 40 * 5308136 * 2
def baseEnd_5308136 : Nat := 2725625147434349127188333

theorem tailTrace_5308136 : CollatzResearch.WordTrace tailWord_5308136 prefixEnd_5308136 2725625147434349127188333 := by
  unfold tailWord_5308136
  simp only [CollatzResearch.WordTrace]
  refine ⟨96801812548768652149592131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129069083398358202866122841 96801812548768652149592131)
  ·
    refine ⟨145202718823152978224388197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96801812548768652149592131 145202718823152978224388197)
    ·
      refine ⟨27225509779341183417072787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145202718823152978224388197 27225509779341183417072787)
      ·
        refine ⟨40838264669011775125609181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27225509779341183417072787 40838264669011775125609181)
        ·
          refine ⟨15314349250879415672103443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40838264669011775125609181 15314349250879415672103443)
          ·
            refine ⟨22971523876319123508155165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15314349250879415672103443 22971523876319123508155165)
            ·
              refine ⟨8614321453619671315558187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22971523876319123508155165 8614321453619671315558187)
              ·
                refine ⟨12921482180429506973337281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8614321453619671315558187 12921482180429506973337281)
                ·
                  refine ⟨9691111635322130230002961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12921482180429506973337281 9691111635322130230002961)
                  ·
                    refine ⟨7268333726491597672502221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9691111635322130230002961 7268333726491597672502221)
                    ·
                      refine ⟨2725625147434349127188333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7268333726491597672502221 2725625147434349127188333)
                      ·
                        rfl

theorem cell23_5308136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_5308136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308136 prefixEnd_5308136 := by exact prefixLift 5308136
  have htrace : WordTrace (prefixWord ++ tailWord_5308136) baseStart_5308136 baseEnd_5308136 := by
    simpa [prefixWord, tailWord_5308136, baseEnd_5308136] using wordTrace_append hprefix tailTrace_5308136
  have hstable : (prefixWord ++ tailWord_5308136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308136).length < 2 ^ (prefixWord ++ tailWord_5308136).sum := by decide
  have hdescent : baseEnd_5308136 < baseStart_5308136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308152 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 5, 5]
def baseStart_5308152 : Nat := 118140960795 + 5308152 * 2 ^ 59
def prefixEnd_5308152 : Nat := 4983230072969 + 3 ^ 40 * 5308152 * 2
def baseEnd_5308152 : Nat := 908544454374940354862753

theorem tailTrace_5308152 : CollatzResearch.WordTrace tailWord_5308152 prefixEnd_5308152 908544454374940354862753 := by
  unfold tailWord_5308152
  simp only [CollatzResearch.WordTrace]
  refine ⟨96802104332739669515883355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129069472443652892687844473 96802104332739669515883355)
  ·
    refine ⟨145203156499109504273825033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96802104332739669515883355 145203156499109504273825033)
    ·
      refine ⟨108902367374332128205368775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145203156499109504273825033 108902367374332128205368775)
      ·
        refine ⟨163353551061498192308053163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108902367374332128205368775 163353551061498192308053163)
        ·
          refine ⟨245030326592247288462079745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163353551061498192308053163 245030326592247288462079745)
          ·
            refine ⟨183772744944185466346559809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245030326592247288462079745 183772744944185466346559809)
            ·
              refine ⟨137829558708139099759919857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183772744944185466346559809 137829558708139099759919857)
              ·
                refine ⟨103372169031104324819939893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137829558708139099759919857 103372169031104324819939893)
                ·
                  refine ⟨9691140846666030451869365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103372169031104324819939893 9691140846666030451869365)
                  ·
                    refine ⟨908544454374940354862753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9691140846666030451869365 908544454374940354862753)
                    ·
                      rfl

theorem cell23_5308152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_5308152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308152 prefixEnd_5308152 := by exact prefixLift 5308152
  have htrace : WordTrace (prefixWord ++ tailWord_5308152) baseStart_5308152 baseEnd_5308152 := by
    simpa [prefixWord, tailWord_5308152, baseEnd_5308152] using wordTrace_append hprefix tailTrace_5308152
  have hstable : (prefixWord ++ tailWord_5308152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308152).length < 2 ^ (prefixWord ++ tailWord_5308152).sum := by decide
  have hdescent : baseEnd_5308152 < baseStart_5308152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308186 : List Nat := [3, 1, 1, 3, 2, 3, 2, 2, 1, 5]
def baseStart_5308186 : Nat := 118140960795 + 5308186 * 2 ^ 59
def prefixEnd_5308186 : Nat := 4983230072969 + 3 ^ 40 * 5308186 * 2
def baseEnd_5308186 : Nat := 908550273822357977187701

theorem tailTrace_5308186 : CollatzResearch.WordTrace tailWord_5308186 prefixEnd_5308186 908550273822357977187701 := by
  unfold tailWord_5308186
  simp only [CollatzResearch.WordTrace]
  refine ⟨48401362186839040709626103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129070299164904108559002941 48401362186839040709626103)
  ·
    refine ⟨72602043280258561064439155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48401362186839040709626103 72602043280258561064439155)
    ·
      refine ⟨108903064920387841596658733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72602043280258561064439155 108903064920387841596658733)
      ·
        refine ⟨40838649345145440598747025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108903064920387841596658733 40838649345145440598747025)
        ·
          refine ⟨30628987008859080449060269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40838649345145440598747025 30628987008859080449060269)
          ·
            refine ⟨11485870128322155168397601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30628987008859080449060269 11485870128322155168397601)
            ·
              refine ⟨8614402596241616376298201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11485870128322155168397601 8614402596241616376298201)
              ·
                refine ⟨6460801947181212282223651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8614402596241616376298201 6460801947181212282223651)
                ·
                  refine ⟨9691202920771818423335477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6460801947181212282223651 9691202920771818423335477)
                  ·
                    refine ⟨908550273822357977187701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9691202920771818423335477 908550273822357977187701)
                    ·
                      rfl

theorem cell23_5308186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_5308186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308186 prefixEnd_5308186 := by exact prefixLift 5308186
  have htrace : WordTrace (prefixWord ++ tailWord_5308186) baseStart_5308186 baseEnd_5308186 := by
    simpa [prefixWord, tailWord_5308186, baseEnd_5308186] using wordTrace_append hprefix tailTrace_5308186
  have hstable : (prefixWord ++ tailWord_5308186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308186).length < 2 ^ (prefixWord ++ tailWord_5308186).sum := by decide
  have hdescent : baseEnd_5308186 < baseStart_5308186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308200 : List Nat := [2, 1, 5, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_5308200 : Nat := 118140960795 + 5308200 * 2 ^ 59
def prefixEnd_5308200 : Nat := 4983230072969 + 3 ^ 40 * 5308200 * 2
def baseEnd_5308200 : Nat := 2725658010196236876788039

theorem tailTrace_5308200 : CollatzResearch.WordTrace tailWord_5308200 prefixEnd_5308200 2725658010196236876788039 := by
  unfold tailWord_5308200
  simp only [CollatzResearch.WordTrace]
  refine ⟨96802979684652721614757027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129070639579536962153009369 96802979684652721614757027)
  ·
    refine ⟨145204469526979082422135541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96802979684652721614757027 145204469526979082422135541)
    ·
      refine ⟨13612919018154288977075207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145204469526979082422135541 13612919018154288977075207)
      ·
        refine ⟨20419378527231433465612811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13612919018154288977075207 20419378527231433465612811)
        ·
          refine ⟨30629067790847150198419217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20419378527231433465612811 30629067790847150198419217)
          ·
            refine ⟨22971800843135362648814413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30629067790847150198419217 22971800843135362648814413)
            ·
              refine ⟨8614425316175760993305405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22971800843135362648814413 8614425316175760993305405)
              ·
                refine ⟨3230409493565910372489527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8614425316175760993305405 3230409493565910372489527)
                ·
                  refine ⟨4845614240348865558734291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3230409493565910372489527 4845614240348865558734291)
                  ·
                    refine ⟨7268421360523298338101437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4845614240348865558734291 7268421360523298338101437)
                    ·
                      refine ⟨2725658010196236876788039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7268421360523298338101437 2725658010196236876788039)
                      ·
                        rfl

theorem cell23_5308200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_5308200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308200 prefixEnd_5308200 := by exact prefixLift 5308200
  have htrace : WordTrace (prefixWord ++ tailWord_5308200) baseStart_5308200 baseEnd_5308200 := by
    simpa [prefixWord, tailWord_5308200, baseEnd_5308200] using wordTrace_append hprefix tailTrace_5308200
  have hstable : (prefixWord ++ tailWord_5308200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308200).length < 2 ^ (prefixWord ++ tailWord_5308200).sum := by decide
  have hdescent : baseEnd_5308200 < baseStart_5308200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308209 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 1, 1, 5]
def baseStart_5308209 : Nat := 118140960795 + 5308209 * 2 ^ 59
def prefixEnd_5308209 : Nat := 4983230072969 + 3 ^ 40 * 5308209 * 2
def baseEnd_5308209 : Nat := 2725662631522127341575497

theorem tailTrace_5308209 : CollatzResearch.WordTrace tailWord_5308209 prefixEnd_5308209 2725662631522127341575497 := by
  unfold tailWord_5308209
  simp only [CollatzResearch.WordTrace]
  refine ⟨193606287626272837766591681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129070858417515225177727787 193606287626272837766591681)
  ·
    refine ⟨145204715719704628324943761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193606287626272837766591681 145204715719704628324943761)
    ·
      refine ⟨108903536789778471243707821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145204715719704628324943761 108903536789778471243707821)
      ·
        refine ⟨40838826296166926716390433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108903536789778471243707821 40838826296166926716390433)
        ·
          refine ⟨30629119722125195037292825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40838826296166926716390433 30629119722125195037292825)
          ·
            refine ⟨22971839791593896277969619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30629119722125195037292825 22971839791593896277969619)
            ·
              refine ⟨34457759687390844416954429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22971839791593896277969619 34457759687390844416954429)
              ·
                refine ⟨12921659882771566656357911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34457759687390844416954429 12921659882771566656357911)
                ·
                  refine ⟨19382489824157349984536867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12921659882771566656357911 19382489824157349984536867)
                  ·
                    refine ⟨29073734736236024976805301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19382489824157349984536867 29073734736236024976805301)
                    ·
                      refine ⟨2725662631522127341575497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29073734736236024976805301 2725662631522127341575497)
                      ·
                        rfl

theorem cell23_5308209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_5308209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308209 prefixEnd_5308209 := by exact prefixLift 5308209
  have htrace : WordTrace (prefixWord ++ tailWord_5308209) baseStart_5308209 baseEnd_5308209 := by
    simpa [prefixWord, tailWord_5308209, baseEnd_5308209] using wordTrace_append hprefix tailTrace_5308209
  have hstable : (prefixWord ++ tailWord_5308209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308209).length < 2 ^ (prefixWord ++ tailWord_5308209).sum := by decide
  have hdescent : baseEnd_5308209 < baseStart_5308209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308217 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 3, 1, 3]
def baseStart_5308217 : Nat := 118140960795 + 5308217 * 2 ^ 59
def prefixEnd_5308217 : Nat := 4983230072969 + 3 ^ 40 * 5308217 * 2
def baseEnd_5308217 : Nat := 2725666739367363310275461

theorem tailTrace_5308217 : CollatzResearch.WordTrace tailWord_5308217 prefixEnd_5308217 2725666739367363310275461 := by
  unfold tailWord_5308217
  simp only [CollatzResearch.WordTrace]
  refine ⟨193606579410243855132882905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129071052940162570088588603 193606579410243855132882905)
  ·
    refine ⟨145204934557682891349662179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193606579410243855132882905 145204934557682891349662179)
    ·
      refine ⟨217807401836524337024493269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145204934557682891349662179 217807401836524337024493269)
      ·
        refine ⟨5104860980543539149011561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 217807401836524337024493269 5104860980543539149011561)
        ·
          refine ⟨3828645735407654361758671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5104860980543539149011561 3828645735407654361758671)
          ·
            refine ⟨5742968603111481542638007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3828645735407654361758671 5742968603111481542638007)
            ·
              refine ⟨8614452904667222313957011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5742968603111481542638007 8614452904667222313957011)
              ·
                refine ⟨12921679357000833470935517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8614452904667222313957011 12921679357000833470935517)
                ·
                  refine ⟨4845629758875312551600819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12921679357000833470935517 4845629758875312551600819)
                  ·
                    refine ⟨7268444638312968827401229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4845629758875312551600819 7268444638312968827401229)
                    ·
                      refine ⟨2725666739367363310275461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7268444638312968827401229 2725666739367363310275461)
                      ·
                        rfl

theorem cell23_5308217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_5308217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308217 prefixEnd_5308217 := by exact prefixLift 5308217
  have htrace : WordTrace (prefixWord ++ tailWord_5308217) baseStart_5308217 baseEnd_5308217 := by
    simpa [prefixWord, tailWord_5308217, baseEnd_5308217] using wordTrace_append hprefix tailTrace_5308217
  have hstable : (prefixWord ++ tailWord_5308217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308217).length < 2 ^ (prefixWord ++ tailWord_5308217).sum := by decide
  have hdescent : baseEnd_5308217 < baseStart_5308217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308256 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 3]
def baseStart_5308256 : Nat := 118140960795 + 5308256 * 2 ^ 59
def prefixEnd_5308256 : Nat := 4983230072969 + 3 ^ 40 * 5308256 * 2
def baseEnd_5308256 : Nat := 2725686765112888657687781

theorem tailTrace_5308256 : CollatzResearch.WordTrace tailWord_5308256 prefixEnd_5308256 2725686765112888657687781 := by
  unfold tailWord_5308256
  simp only [CollatzResearch.WordTrace]
  refine ⟨96804000928551282396776311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129072001238068376529035081 96804000928551282396776311)
  ·
    refine ⟨145206001392826923595164467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96804000928551282396776311 145206001392826923595164467)
    ·
      refine ⟨217809002089240385392746701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145206001392826923595164467 217809002089240385392746701)
      ·
        refine ⟨81678375783465144522280013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217809002089240385392746701 81678375783465144522280013)
        ·
          refine ⟨30629390918799429195855005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81678375783465144522280013 30629390918799429195855005)
          ·
            refine ⟨11486021594549785948445627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30629390918799429195855005 11486021594549785948445627)
            ·
              refine ⟨17229032391824678922668441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11486021594549785948445627 17229032391824678922668441)
              ·
                refine ⟨12921774293868509192001331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17229032391824678922668441 12921774293868509192001331)
                ·
                  refine ⟨19382661440802763788001997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12921774293868509192001331 19382661440802763788001997)
                  ·
                    refine ⟨7268498040301036420500749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19382661440802763788001997 7268498040301036420500749)
                    ·
                      refine ⟨2725686765112888657687781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7268498040301036420500749 2725686765112888657687781)
                      ·
                        rfl

theorem cell23_5308256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_5308256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308256 prefixEnd_5308256 := by exact prefixLift 5308256
  have htrace : WordTrace (prefixWord ++ tailWord_5308256) baseStart_5308256 baseEnd_5308256 := by
    simpa [prefixWord, tailWord_5308256, baseEnd_5308256] using wordTrace_append hprefix tailTrace_5308256
  have hstable : (prefixWord ++ tailWord_5308256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308256).length < 2 ^ (prefixWord ++ tailWord_5308256).sum := by decide
  have hdescent : baseEnd_5308256 < baseStart_5308256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308260 : List Nat := [2, 3, 1, 1, 5, 1, 3, 1, 1, 2, 3]
def baseStart_5308260 : Nat := 118140960795 + 5308260 * 2 ^ 59
def prefixEnd_5308260 : Nat := 4983230072969 + 3 ^ 40 * 5308260 * 2
def baseEnd_5308260 : Nat := 2725688819035506642037763

theorem tailTrace_5308260 : CollatzResearch.WordTrace tailWord_5308260 prefixEnd_5308260 2725688819035506642037763 := by
  unfold tailWord_5308260
  simp only [CollatzResearch.WordTrace]
  refine ⟨96804073874544036738349117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129072098499392048984465489 96804073874544036738349117)
  ·
    refine ⟨36301527702954013776880919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96804073874544036738349117 36301527702954013776880919)
    ·
      refine ⟨54452291554431020665321379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36301527702954013776880919 54452291554431020665321379)
      ·
        refine ⟨81678437331646530997982069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54452291554431020665321379 81678437331646530997982069)
        ·
          refine ⟨7657353499841862281060819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81678437331646530997982069 7657353499841862281060819)
          ·
            refine ⟨11486030249762793421591229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7657353499841862281060819 11486030249762793421591229)
            ·
              refine ⟨4307261343661047533096711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11486030249762793421591229 4307261343661047533096711)
              ·
                refine ⟨6460892015491571299645067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4307261343661047533096711 6460892015491571299645067)
                ·
                  refine ⟨9691338023237356949467601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6460892015491571299645067 9691338023237356949467601)
                  ·
                    refine ⟨7268503517428017712100701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9691338023237356949467601 7268503517428017712100701)
                    ·
                      refine ⟨2725688819035506642037763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7268503517428017712100701 2725688819035506642037763)
                      ·
                        rfl

theorem cell23_5308260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_5308260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308260 prefixEnd_5308260 := by exact prefixLift 5308260
  have htrace : WordTrace (prefixWord ++ tailWord_5308260) baseStart_5308260 baseEnd_5308260 := by
    simpa [prefixWord, tailWord_5308260, baseEnd_5308260] using wordTrace_append hprefix tailTrace_5308260
  have hstable : (prefixWord ++ tailWord_5308260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308260).length < 2 ^ (prefixWord ++ tailWord_5308260).sum := by decide
  have hdescent : baseEnd_5308260 < baseStart_5308260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308269 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_5308269 : Nat := 118140960795 + 5308269 * 2 ^ 59
def prefixEnd_5308269 : Nat := 4983230072969 + 3 ^ 40 * 5308269 * 2
def baseEnd_5308269 : Nat := 2725693440361397106825221

theorem tailTrace_5308269 : CollatzResearch.WordTrace tailWord_5308269 prefixEnd_5308269 2725693440361397106825221 := by
  unfold tailWord_5308269
  simp only [CollatzResearch.WordTrace]
  refine ⟨193608476006055468013775861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129072317337370312009183907 193608476006055468013775861)
  ·
    refine ⟨18150794625567700126291487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193608476006055468013775861 18150794625567700126291487)
    ·
      refine ⟨27226191938351550189437231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18150794625567700126291487 27226191938351550189437231)
      ·
        refine ⟨40839287907527325284155847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27226191938351550189437231 40839287907527325284155847)
        ·
          refine ⟨61258931861290987926233771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40839287907527325284155847 61258931861290987926233771)
          ·
            refine ⟨91888397791936481889350657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61258931861290987926233771 91888397791936481889350657)
            ·
              refine ⟨68916298343952361417012993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91888397791936481889350657 68916298343952361417012993)
              ·
                refine ⟨51687223757964271062759745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68916298343952361417012993 51687223757964271062759745)
                ·
                  refine ⟨38765417818473203297069809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51687223757964271062759745 38765417818473203297069809)
                  ·
                    refine ⟨29074063363854902472802357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38765417818473203297069809 29074063363854902472802357)
                    ·
                      refine ⟨2725693440361397106825221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29074063363854902472802357 2725693440361397106825221)
                      ·
                        rfl

theorem cell23_5308269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_5308269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308269 prefixEnd_5308269 := by exact prefixLift 5308269
  have htrace : WordTrace (prefixWord ++ tailWord_5308269) baseStart_5308269 baseEnd_5308269 := by
    simpa [prefixWord, tailWord_5308269, baseEnd_5308269] using wordTrace_append hprefix tailTrace_5308269
  have hstable : (prefixWord ++ tailWord_5308269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308269).length < 2 ^ (prefixWord ++ tailWord_5308269).sum := by decide
  have hdescent : baseEnd_5308269 < baseStart_5308269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308273 : List Nat := [1, 2, 2, 2, 1, 3, 4, 2, 2, 1, 3]
def baseStart_5308273 : Nat := 118140960795 + 5308273 * 2 ^ 59
def prefixEnd_5308273 : Nat := 4983230072969 + 3 ^ 40 * 5308273 * 2
def baseEnd_5308273 : Nat := 2725695494284015091175203

theorem tailTrace_5308273 : CollatzResearch.WordTrace tailWord_5308273 prefixEnd_5308273 2725695494284015091175203 := by
  unfold tailWord_5308273
  simp only [CollatzResearch.WordTrace]
  refine ⟨193608621898040976696921473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129072414598693984464614315 193608621898040976696921473)
  ·
    refine ⟨145206466423530732522691105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193608621898040976696921473 145206466423530732522691105)
    ·
      refine ⟨108904849817648049392018329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145206466423530732522691105 108904849817648049392018329)
      ·
        refine ⟨81678637363236037044013747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108904849817648049392018329 81678637363236037044013747)
        ·
          refine ⟨122517956044854055566020621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81678637363236037044013747 122517956044854055566020621)
          ·
            refine ⟨45944233516820270837257733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122517956044854055566020621 45944233516820270837257733)
            ·
              refine ⟨8614543784403800781985825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45944233516820270837257733 8614543784403800781985825)
              ·
                refine ⟨6460907838302850586489369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8614543784403800781985825 6460907838302850586489369)
                ·
                  refine ⟨4845680878727137939867027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6460907838302850586489369 4845680878727137939867027)
                  ·
                    refine ⟨7268521318090706909800541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4845680878727137939867027 7268521318090706909800541)
                    ·
                      refine ⟨2725695494284015091175203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7268521318090706909800541 2725695494284015091175203)
                      ·
                        rfl

theorem cell23_5308273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_5308273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308273 prefixEnd_5308273 := by exact prefixLift 5308273
  have htrace : WordTrace (prefixWord ++ tailWord_5308273) baseStart_5308273 baseEnd_5308273 := by
    simpa [prefixWord, tailWord_5308273, baseEnd_5308273] using wordTrace_append hprefix tailTrace_5308273
  have hstable : (prefixWord ++ tailWord_5308273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308273).length < 2 ^ (prefixWord ++ tailWord_5308273).sum := by decide
  have hdescent : baseEnd_5308273 < baseStart_5308273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308299 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 3]
def baseStart_5308299 : Nat := 118140960795 + 5308299 * 2 ^ 59
def prefixEnd_5308299 : Nat := 4983230072969 + 3 ^ 40 * 5308299 * 2
def baseEnd_5308299 : Nat := 2725708844781031989450083

theorem tailTrace_5308299 : CollatzResearch.WordTrace tailWord_5308299 prefixEnd_5308299 2725708844781031989450083 := by
  unfold tailWord_5308299
  simp only [CollatzResearch.WordTrace]
  refine ⟨193609570195946783137367951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129073046797297855424911967 193609570195946783137367951)
  ·
    refine ⟨290414355293920174706051927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193609570195946783137367951 290414355293920174706051927)
    ·
      refine ⟨435621532940880262059077891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290414355293920174706051927 435621532940880262059077891)
      ·
        refine ⟨653432299411320393088616837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435621532940880262059077891 653432299411320393088616837)
        ·
          refine ⟨122518556139622573704115657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 653432299411320393088616837 122518556139622573704115657)
          ·
            refine ⟨91888917104716930278086743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122518556139622573704115657 91888917104716930278086743)
            ·
              refine ⟨137833375657075395417130115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91888917104716930278086743 137833375657075395417130115)
              ·
                refine ⟨206750063485613093125695173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137833375657075395417130115 206750063485613093125695173)
                ·
                  refine ⟨38765636903552454961067845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 206750063485613093125695173 38765636903552454961067845)
                  ·
                    refine ⟨7268556919416085305200221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38765636903552454961067845 7268556919416085305200221)
                    ·
                      refine ⟨2725708844781031989450083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7268556919416085305200221 2725708844781031989450083)
                      ·
                        rfl

theorem cell23_5308299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 4, 3].length) (baseStart_5308299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308299 prefixEnd_5308299 := by exact prefixLift 5308299
  have htrace : WordTrace (prefixWord ++ tailWord_5308299) baseStart_5308299 baseEnd_5308299 := by
    simpa [prefixWord, tailWord_5308299, baseEnd_5308299] using wordTrace_append hprefix tailTrace_5308299
  have hstable : (prefixWord ++ tailWord_5308299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308299).length < 2 ^ (prefixWord ++ tailWord_5308299).sum := by decide
  have hdescent : baseEnd_5308299 < baseStart_5308299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308309 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_5308309 : Nat := 118140960795 + 5308309 * 2 ^ 59
def prefixEnd_5308309 : Nat := 4983230072969 + 3 ^ 40 * 5308309 * 2
def baseEnd_5308309 : Nat := 2725713979587576950325037

theorem tailTrace_5308309 : CollatzResearch.WordTrace tailWord_5308309 prefixEnd_5308309 2725713979587576950325037 := by
  unfold tailWord_5308309
  simp only [CollatzResearch.WordTrace]
  refine ⟨193609934925910554845231981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129073289950607036563487987 193609934925910554845231981)
  ·
    refine ⟨72603725597216458066961993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193609934925910554845231981 72603725597216458066961993)
    ·
      refine ⟨54452794197912343550221495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72603725597216458066961993 54452794197912343550221495)
      ·
        refine ⟨81679191296868515325332243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54452794197912343550221495 81679191296868515325332243)
        ·
          refine ⟨122518786945302772987998365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81679191296868515325332243 122518786945302772987998365)
          ·
            refine ⟨45944545104488539870499387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122518786945302772987998365 45944545104488539870499387)
            ·
              refine ⟨68916817656732809805749081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45944545104488539870499387 68916817656732809805749081)
              ·
                refine ⟨51687613242549607354311811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68916817656732809805749081 51687613242549607354311811)
                ·
                  refine ⟨77531419863824411031467717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51687613242549607354311811 77531419863824411031467717)
                  ·
                    refine ⟨14537141224467077068400197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77531419863824411031467717 14537141224467077068400197)
                    ·
                      refine ⟨2725713979587576950325037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14537141224467077068400197 2725713979587576950325037)
                      ·
                        rfl

theorem cell23_5308309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_5308309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308309 prefixEnd_5308309 := by exact prefixLift 5308309
  have htrace : WordTrace (prefixWord ++ tailWord_5308309) baseStart_5308309 baseEnd_5308309 := by
    simpa [prefixWord, tailWord_5308309, baseEnd_5308309] using wordTrace_append hprefix tailTrace_5308309
  have hstable : (prefixWord ++ tailWord_5308309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308309).length < 2 ^ (prefixWord ++ tailWord_5308309).sum := by decide
  have hdescent : baseEnd_5308309 < baseStart_5308309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308317 : List Nat := [1, 4, 2, 1, 2, 4, 2, 1, 1, 3, 2]
def baseStart_5308317 : Nat := 118140960795 + 5308317 * 2 ^ 59
def prefixEnd_5308317 : Nat := 4983230072969 + 3 ^ 40 * 5308317 * 2
def baseEnd_5308317 : Nat := 2725718087432812919025001

theorem tailTrace_5308317 : CollatzResearch.WordTrace tailWord_5308317 prefixEnd_5308317 2725718087432812919025001 := by
  unfold tailWord_5308317
  simp only [CollatzResearch.WordTrace]
  refine ⟨193610226709881572211523205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129073484473254381474348803 193610226709881572211523205)
  ·
    refine ⟨36301917508102794789660601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193610226709881572211523205 36301917508102794789660601)
    ·
      refine ⟨27226438131077096092245451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36301917508102794789660601 27226438131077096092245451)
      ·
        refine ⟨40839657196615644138368177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27226438131077096092245451 40839657196615644138368177)
        ·
          refine ⟨30629742897461733103776133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40839657196615644138368177 30629742897461733103776133)
          ·
            refine ⟨5743076793274074956958025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30629742897461733103776133 5743076793274074956958025)
            ·
              refine ⟨4307307594955556217718519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5743076793274074956958025 4307307594955556217718519)
              ·
                refine ⟨6460961392433334326577779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4307307594955556217718519 6460961392433334326577779)
                ·
                  refine ⟨9691442088650001489866669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6460961392433334326577779 9691442088650001489866669)
                  ·
                    refine ⟨3634290783243750558700001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9691442088650001489866669 3634290783243750558700001)
                    ·
                      refine ⟨2725718087432812919025001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3634290783243750558700001 2725718087432812919025001)
                      ·
                        rfl

theorem cell23_5308317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_5308317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308317 prefixEnd_5308317 := by exact prefixLift 5308317
  have htrace : WordTrace (prefixWord ++ tailWord_5308317) baseStart_5308317 baseEnd_5308317 := by
    simpa [prefixWord, tailWord_5308317, baseEnd_5308317] using wordTrace_append hprefix tailTrace_5308317
  have hstable : (prefixWord ++ tailWord_5308317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308317).length < 2 ^ (prefixWord ++ tailWord_5308317).sum := by decide
  have hdescent : baseEnd_5308317 < baseStart_5308317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308359 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 5]
def baseStart_5308359 : Nat := 118140960795 + 5308359 * 2 ^ 59
def prefixEnd_5308359 : Nat := 4983230072969 + 3 ^ 40 * 5308359 * 2
def baseEnd_5308359 : Nat := 2725739653620301754699807

theorem tailTrace_5308359 : CollatzResearch.WordTrace tailWord_5308359 prefixEnd_5308359 2725739653620301754699807 := by
  unfold tailWord_5308359
  simp only [CollatzResearch.WordTrace]
  refine ⟨193611758575729413384552131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129074505717152942256368087 193611758575729413384552131)
  ·
    refine ⟨290417637863594120076828197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193611758575729413384552131 290417637863594120076828197)
    ·
      refine ⟨54453307099423897514405287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290417637863594120076828197 54453307099423897514405287)
      ·
        refine ⟨81679960649135846271607931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54453307099423897514405287 81679960649135846271607931)
        ·
          refine ⟨122519940973703769407411897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81679960649135846271607931 122519940973703769407411897)
          ·
            refine ⟨91889955730277827055558923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122519940973703769407411897 91889955730277827055558923)
            ·
              refine ⟨137834933595416740583338385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91889955730277827055558923 137834933595416740583338385)
              ·
                refine ⟨103376200196562555437503789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137834933595416740583338385 103376200196562555437503789)
                ·
                  refine ⟨38766075073710958289063921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103376200196562555437503789 38766075073710958289063921)
                  ·
                    refine ⟨29074556305283218716797941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38766075073710958289063921 29074556305283218716797941)
                    ·
                      refine ⟨2725739653620301754699807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29074556305283218716797941 2725739653620301754699807)
                      ·
                        rfl

theorem cell23_5308359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_5308359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308359 prefixEnd_5308359 := by exact prefixLift 5308359
  have htrace : WordTrace (prefixWord ++ tailWord_5308359) baseStart_5308359 baseEnd_5308359 := by
    simpa [prefixWord, tailWord_5308359, baseEnd_5308359] using wordTrace_append hprefix tailTrace_5308359
  have hstable : (prefixWord ++ tailWord_5308359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308359).length < 2 ^ (prefixWord ++ tailWord_5308359).sum := by decide
  have hdescent : baseEnd_5308359 < baseStart_5308359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308366 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_5308366 : Nat := 118140960795 + 5308366 * 2 ^ 59
def prefixEnd_5308366 : Nat := 4983230072969 + 3 ^ 40 * 5308366 * 2
def baseEnd_5308366 : Nat := 908581082661627742437425

theorem tailTrace_5308366 : CollatzResearch.WordTrace tailWord_5308366 prefixEnd_5308366 908581082661627742437425 := by
  unfold tailWord_5308366
  simp only [CollatzResearch.WordTrace]
  refine ⟨24201501735838006697507119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129074675924469369053371301 24201501735838006697507119)
  ·
    refine ⟨36302252603757010046260679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24201501735838006697507119 36302252603757010046260679)
    ·
      refine ⟨54453378905635515069391019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36302252603757010046260679 54453378905635515069391019)
      ·
        refine ⟨81680068358453272604086529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54453378905635515069391019 81680068358453272604086529)
        ·
          refine ⟨61260051268839954453064897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81680068358453272604086529 61260051268839954453064897)
          ·
            refine ⟨45945038451629965839798673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61260051268839954453064897 45945038451629965839798673)
            ·
              refine ⟨34458778838722474379849005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45945038451629965839798673 34458778838722474379849005)
              ·
                refine ⟨12922042064520927892443377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34458778838722474379849005 12922042064520927892443377)
                ·
                  refine ⟨9691531548390695919332533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12922042064520927892443377 9691531548390695919332533)
                  ·
                    refine ⟨908581082661627742437425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9691531548390695919332533 908581082661627742437425)
                    ·
                      rfl

theorem cell23_5308366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_5308366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308366 prefixEnd_5308366 := by exact prefixLift 5308366
  have htrace : WordTrace (prefixWord ++ tailWord_5308366) baseStart_5308366 baseEnd_5308366 := by
    simpa [prefixWord, tailWord_5308366, baseEnd_5308366] using wordTrace_append hprefix tailTrace_5308366
  have hstable : (prefixWord ++ tailWord_5308366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308366).length < 2 ^ (prefixWord ++ tailWord_5308366).sum := by decide
  have hdescent : baseEnd_5308366 < baseStart_5308366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308423 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 3]
def baseStart_5308423 : Nat := 118140960795 + 5308423 * 2 ^ 59
def prefixEnd_5308423 : Nat := 4983230072969 + 3 ^ 40 * 5308423 * 2
def baseEnd_5308423 : Nat := 2725772516382189504299513

theorem tailTrace_5308423 : CollatzResearch.WordTrace tailWord_5308423 prefixEnd_5308423 2725772516382189504299513 := by
  unfold tailWord_5308423
  simp only [CollatzResearch.WordTrace]
  refine ⟨193614092847497552314881923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129076061898331701543254615 193614092847497552314881923)
  ·
    refine ⟨290421139271246328472322885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193614092847497552314881923 290421139271246328472322885)
    ·
      refine ⟨54453963613358686588560541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290421139271246328472322885 54453963613358686588560541)
      ·
        refine ⟨20420236355009507470710203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54453963613358686588560541 20420236355009507470710203)
        ·
          refine ⟨30630354532514261206065305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20420236355009507470710203 30630354532514261206065305)
          ·
            refine ⟨22972765899385695904548979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30630354532514261206065305 22972765899385695904548979)
            ·
              refine ⟨34459148849078543856823469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22972765899385695904548979 34459148849078543856823469)
              ·
                refine ⟨12922180818404453946308801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34459148849078543856823469 12922180818404453946308801)
                ·
                  refine ⟨9691635613803340459731601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12922180818404453946308801 9691635613803340459731601)
                  ·
                    refine ⟨7268726710352505344798701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9691635613803340459731601 7268726710352505344798701)
                    ·
                      refine ⟨2725772516382189504299513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7268726710352505344798701 2725772516382189504299513)
                      ·
                        rfl

theorem cell23_5308423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_5308423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308423 prefixEnd_5308423 := by exact prefixLift 5308423
  have htrace : WordTrace (prefixWord ++ tailWord_5308423) baseStart_5308423 baseEnd_5308423 := by
    simpa [prefixWord, tailWord_5308423, baseEnd_5308423] using wordTrace_append hprefix tailTrace_5308423
  have hstable : (prefixWord ++ tailWord_5308423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308423).length < 2 ^ (prefixWord ++ tailWord_5308423).sum := by decide
  have hdescent : baseEnd_5308423 < baseStart_5308423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308430 : List Nat := [4, 1, 1, 2, 2, 1, 2, 5, 1, 4]
def baseStart_5308430 : Nat := 118140960795 + 5308430 * 2 ^ 59
def prefixEnd_5308430 : Nat := 4983230072969 + 3 ^ 40 * 5308430 * 2
def baseEnd_5308430 : Nat := 908592036915590325637327

theorem tailTrace_5308430 : CollatzResearch.WordTrace tailWord_5308430 prefixEnd_5308430 908592036915590325637327 := by
  unfold tailWord_5308430
  simp only [CollatzResearch.WordTrace]
  refine ⟨24201793519809024063798343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129076232105648128340257829 24201793519809024063798343)
  ·
    refine ⟨36302690279713536095697515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24201793519809024063798343 36302690279713536095697515)
    ·
      refine ⟨54454035419570304143546273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36302690279713536095697515 54454035419570304143546273)
      ·
        refine ⟨40840526564677728107659705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54454035419570304143546273 40840526564677728107659705)
        ·
          refine ⟨30630394923508296080744779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40840526564677728107659705 30630394923508296080744779)
          ·
            refine ⟨45945592385262444121117169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30630394923508296080744779 45945592385262444121117169)
            ·
              refine ⟨34459194288946833090837877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45945592385262444121117169 34459194288946833090837877)
              ·
                refine ⟨3230549464588765602266051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34459194288946833090837877 3230549464588765602266051)
                ·
                  refine ⟨4845824196883148403399077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3230549464588765602266051 4845824196883148403399077)
                  ·
                    refine ⟨908592036915590325637327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4845824196883148403399077 908592036915590325637327)
                    ·
                      rfl

theorem cell23_5308430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_5308430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308430 prefixEnd_5308430 := by exact prefixLift 5308430
  have htrace : WordTrace (prefixWord ++ tailWord_5308430) baseStart_5308430 baseEnd_5308430 := by
    simpa [prefixWord, tailWord_5308430, baseEnd_5308430] using wordTrace_append hprefix tailTrace_5308430
  have hstable : (prefixWord ++ tailWord_5308430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308430).length < 2 ^ (prefixWord ++ tailWord_5308430).sum := by decide
  have hdescent : baseEnd_5308430 < baseStart_5308430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308480 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 2, 3, 2]
def baseStart_5308480 : Nat := 118140960795 + 5308480 * 2 ^ 59
def prefixEnd_5308480 : Nat := 4983230072969 + 3 ^ 40 * 5308480 * 2
def baseEnd_5308480 : Nat := 2725801784779495781286751

theorem tailTrace_5308480 : CollatzResearch.WordTrace tailWord_5308480 prefixEnd_5308480 2725801784779495781286751 := by
  unfold tailWord_5308480
  simp only [CollatzResearch.WordTrace]
  refine ⟨96808085904145525524853447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129077447872194034033137929 96808085904145525524853447)
  ·
    refine ⟨145212128856218288287280171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96808085904145525524853447 145212128856218288287280171)
    ·
      refine ⟨217818193284327432430920257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145212128856218288287280171 217818193284327432430920257)
      ·
        refine ⟨163363644963245574323190193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217818193284327432430920257 163363644963245574323190193)
        ·
          refine ⟨122522733722434180742392645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163363644963245574323190193 122522733722434180742392645)
          ·
            refine ⟨22973012572956408889198621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122522733722434180742392645 22973012572956408889198621)
            ·
              refine ⟨8614879714858653333449483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22973012572956408889198621 8614879714858653333449483)
              ·
                refine ⟨12922319572287980000174225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8614879714858653333449483 12922319572287980000174225)
                ·
                  refine ⟨9691739679215985000130669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12922319572287980000174225 9691739679215985000130669)
                  ·
                    refine ⟨3634402379705994375049001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9691739679215985000130669 3634402379705994375049001)
                    ·
                      refine ⟨2725801784779495781286751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3634402379705994375049001 2725801784779495781286751)
                      ·
                        rfl

theorem cell23_5308480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 2, 3, 2].length) (baseStart_5308480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308480 prefixEnd_5308480 := by exact prefixLift 5308480
  have htrace : WordTrace (prefixWord ++ tailWord_5308480) baseStart_5308480 baseEnd_5308480 := by
    simpa [prefixWord, tailWord_5308480, baseEnd_5308480] using wordTrace_append hprefix tailTrace_5308480
  have hstable : (prefixWord ++ tailWord_5308480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308480).length < 2 ^ (prefixWord ++ tailWord_5308480).sum := by decide
  have hdescent : baseEnd_5308480 < baseStart_5308480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308487 : List Nat := [1, 1, 4, 1, 3, 1, 4, 3, 1, 1, 3]
def baseStart_5308487 : Nat := 118140960795 + 5308487 * 2 ^ 59
def prefixEnd_5308487 : Nat := 4983230072969 + 3 ^ 40 * 5308487 * 2
def baseEnd_5308487 : Nat := 2725805379144077253899219

theorem tailTrace_5308487 : CollatzResearch.WordTrace tailWord_5308487 prefixEnd_5308487 2725805379144077253899219 := by
  unfold tailWord_5308487
  simp only [CollatzResearch.WordTrace]
  refine ⟨193616427119265691245211715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129077618079510460830141143 193616427119265691245211715)
  ·
    refine ⟨290424640678898536867817573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193616427119265691245211715 290424640678898536867817573)
    ·
      refine ⟨54454620127293475662715795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290424640678898536867817573 54454620127293475662715795)
      ·
        refine ⟨81681930190940213494073693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54454620127293475662715795 81681930190940213494073693)
        ·
          refine ⟨30630723821602580060277635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81681930190940213494073693 30630723821602580060277635)
          ·
            refine ⟨45946085732403870090416453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30630723821602580060277635 45946085732403870090416453)
            ·
              refine ⟨8614891074825725641953085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45946085732403870090416453 8614891074825725641953085)
              ·
                refine ⟨3230584153059647115732407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8614891074825725641953085 3230584153059647115732407)
                ·
                  refine ⟨4845876229589470673598611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3230584153059647115732407 4845876229589470673598611)
                  ·
                    refine ⟨7268814344384206010397917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4845876229589470673598611 7268814344384206010397917)
                    ·
                      refine ⟨2725805379144077253899219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7268814344384206010397917 2725805379144077253899219)
                      ·
                        rfl

theorem cell23_5308487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_5308487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308487 prefixEnd_5308487 := by exact prefixLift 5308487
  have htrace : WordTrace (prefixWord ++ tailWord_5308487) baseStart_5308487 baseEnd_5308487 := by
    simpa [prefixWord, tailWord_5308487, baseEnd_5308487] using wordTrace_append hprefix tailTrace_5308487
  have hstable : (prefixWord ++ tailWord_5308487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308487).length < 2 ^ (prefixWord ++ tailWord_5308487).sum := by decide
  have hdescent : baseEnd_5308487 < baseStart_5308487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308506 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6]
def baseStart_5308506 : Nat := 118140960795 + 5308506 * 2 ^ 59
def prefixEnd_5308506 : Nat := 4983230072969 + 3 ^ 40 * 5308506 * 2
def baseEnd_5308506 : Nat := 2725815135276512679561631

theorem tailTrace_5308506 : CollatzResearch.WordTrace tailWord_5308506 prefixEnd_5308506 2725815135276512679561631 := by
  unfold tailWord_5308506
  simp only [CollatzResearch.WordTrace]
  refine ⟨48404280026549214372538343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129078080070797904993435581 48404280026549214372538343)
  ·
    refine ⟨72606420039823821558807515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48404280026549214372538343 72606420039823821558807515)
    ·
      refine ⟨108909630059735732338211273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72606420039823821558807515 108909630059735732338211273)
      ·
        refine ⟨81682222544801799253658455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108909630059735732338211273 81682222544801799253658455)
        ·
          refine ⟨122523333817202698880487683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81682222544801799253658455 122523333817202698880487683)
          ·
            refine ⟨183785000725804048320731525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122523333817202698880487683 183785000725804048320731525)
            ·
              refine ⟨34459687636088259060137161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183785000725804048320731525 34459687636088259060137161)
              ·
                refine ⟨25844765727066194295102871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34459687636088259060137161 25844765727066194295102871)
                ·
                  refine ⟨38767148590599291442654307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25844765727066194295102871 38767148590599291442654307)
                  ·
                    refine ⟨58150722885898937163981461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38767148590599291442654307 58150722885898937163981461)
                    ·
                      refine ⟨2725815135276512679561631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58150722885898937163981461 2725815135276512679561631)
                      ·
                        rfl

theorem cell23_5308506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_5308506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308506 prefixEnd_5308506 := by exact prefixLift 5308506
  have htrace : WordTrace (prefixWord ++ tailWord_5308506) baseStart_5308506 baseEnd_5308506 := by
    simpa [prefixWord, tailWord_5308506, baseEnd_5308506] using wordTrace_append hprefix tailTrace_5308506
  have hstable : (prefixWord ++ tailWord_5308506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308506).length < 2 ^ (prefixWord ++ tailWord_5308506).sum := by decide
  have hdescent : baseEnd_5308506 < baseStart_5308506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308530 : List Nat := [3, 2, 1, 2, 2, 2, 1, 4, 1, 2, 3]
def baseStart_5308530 : Nat := 118140960795 + 5308530 * 2 ^ 59
def prefixEnd_5308530 : Nat := 4983230072969 + 3 ^ 40 * 5308530 * 2
def baseEnd_5308530 : Nat := 2725827458812220585661521

theorem tailTrace_5308530 : CollatzResearch.WordTrace tailWord_5308530 prefixEnd_5308530 2725827458812220585661521 := by
  unfold tailWord_5308530
  simp only [CollatzResearch.WordTrace]
  refine ⟨48404498864527477397256761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129078663638739939726018029 48404498864527477397256761)
  ·
    refine ⟨36303374148395608047942571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48404498864527477397256761 36303374148395608047942571)
    ·
      refine ⟨54455061222593412071913857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36303374148395608047942571 54455061222593412071913857)
      ·
        refine ⟨40841295916945059053935393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54455061222593412071913857 40841295916945059053935393)
        ·
          refine ⟨30630971937708794290451545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40841295916945059053935393 30630971937708794290451545)
          ·
            refine ⟨22973228953281595717838659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30630971937708794290451545 22973228953281595717838659)
            ·
              refine ⟨34459843429922393576757989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22973228953281595717838659 34459843429922393576757989)
              ·
                refine ⟨6461220643110448795642123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34459843429922393576757989 6461220643110448795642123)
                ·
                  refine ⟨9691830964665673193463185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6461220643110448795642123 9691830964665673193463185)
                  ·
                    refine ⟨7268873223499254895097389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9691830964665673193463185 7268873223499254895097389)
                    ·
                      refine ⟨2725827458812220585661521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7268873223499254895097389 2725827458812220585661521)
                      ·
                        rfl

theorem cell23_5308530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_5308530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308530 prefixEnd_5308530 := by exact prefixLift 5308530
  have htrace : WordTrace (prefixWord ++ tailWord_5308530) baseStart_5308530 baseEnd_5308530 := by
    simpa [prefixWord, tailWord_5308530, baseEnd_5308530] using wordTrace_append hprefix tailTrace_5308530
  have hstable : (prefixWord ++ tailWord_5308530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308530).length < 2 ^ (prefixWord ++ tailWord_5308530).sum := by decide
  have hdescent : baseEnd_5308530 < baseStart_5308530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308560 : List Nat := [2, 1, 1, 1, 1, 1, 6, 4, 2, 1, 3]
def baseStart_5308560 : Nat := 118140960795 + 5308560 * 2 ^ 59
def prefixEnd_5308560 : Nat := 4983230072969 + 3 ^ 40 * 5308560 * 2
def baseEnd_5308560 : Nat := 2725842863231855468286383

theorem tailTrace_5308560 : CollatzResearch.WordTrace tailWord_5308560 prefixEnd_5308560 2725842863231855468286383 := by
  unfold tailWord_5308560
  simp only [CollatzResearch.WordTrace]
  refine ⟨96809544824000612356309567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129079393098667483141746089 96809544824000612356309567)
  ·
    refine ⟨145214317236000918534464351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96809544824000612356309567 145214317236000918534464351)
    ·
      refine ⟨217821475854001377801696527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145214317236000918534464351 217821475854001377801696527)
      ·
        refine ⟨326732213781002066702544791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217821475854001377801696527 326732213781002066702544791)
        ·
          refine ⟨490098320671503100053817187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326732213781002066702544791 490098320671503100053817187)
          ·
            refine ⟨735147481007254650080725781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490098320671503100053817187 735147481007254650080725781)
            ·
              refine ⟨34460038172215061722534021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 735147481007254650080725781 34460038172215061722534021)
              ·
                refine ⟨6461257157290324072975129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34460038172215061722534021 6461257157290324072975129)
                ·
                  refine ⟨4845942867967743054731347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6461257157290324072975129 4845942867967743054731347)
                  ·
                    refine ⟨7268914301951614582097021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4845942867967743054731347 7268914301951614582097021)
                    ·
                      refine ⟨2725842863231855468286383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7268914301951614582097021 2725842863231855468286383)
                      ·
                        rfl

theorem cell23_5308560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 2, 1, 3].length) (baseStart_5308560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308560 prefixEnd_5308560 := by exact prefixLift 5308560
  have htrace : WordTrace (prefixWord ++ tailWord_5308560) baseStart_5308560 baseEnd_5308560 := by
    simpa [prefixWord, tailWord_5308560, baseEnd_5308560] using wordTrace_append hprefix tailTrace_5308560
  have hstable : (prefixWord ++ tailWord_5308560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308560).length < 2 ^ (prefixWord ++ tailWord_5308560).sum := by decide
  have hdescent : baseEnd_5308560 < baseStart_5308560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308577 : List Nat := [1, 2, 3, 3, 1, 3, 1, 3, 2, 1, 3]
def baseStart_5308577 : Nat := 118140960795 + 5308577 * 2 ^ 59
def prefixEnd_5308577 : Nat := 4983230072969 + 3 ^ 40 * 5308577 * 2
def baseEnd_5308577 : Nat := 2725851592402981901773805

theorem tailTrace_5308577 : CollatzResearch.WordTrace tailWord_5308577 prefixEnd_5308577 2725851592402981901773805 := by
  unfold tailWord_5308577
  simp only [CollatzResearch.WordTrace]
  refine ⟨193619709688939636615987985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129079806459293091077325323 193619709688939636615987985)
  ·
    refine ⟨145214782266704727461990989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193619709688939636615987985 145214782266704727461990989)
    ·
      refine ⟨54455543350014272798246621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145214782266704727461990989 54455543350014272798246621)
      ·
        refine ⟨20420828756255352299342483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54455543350014272798246621 20420828756255352299342483)
        ·
          refine ⟨30631243134383028449013725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20420828756255352299342483 30631243134383028449013725)
          ·
            refine ⟨11486716175393635668380147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30631243134383028449013725 11486716175393635668380147)
            ·
              refine ⟨17230074263090453502570221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11486716175393635668380147 17230074263090453502570221)
              ·
                refine ⟨6461277848658920063463833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17230074263090453502570221 6461277848658920063463833)
                ·
                  refine ⟨4845958386494190047597875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6461277848658920063463833 4845958386494190047597875)
                  ·
                    refine ⟨7268937579741285071396813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4845958386494190047597875 7268937579741285071396813)
                    ·
                      refine ⟨2725851592402981901773805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7268937579741285071396813 2725851592402981901773805)
                      ·
                        rfl

theorem cell23_5308577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_5308577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308577 prefixEnd_5308577 := by exact prefixLift 5308577
  have htrace : WordTrace (prefixWord ++ tailWord_5308577) baseStart_5308577 baseEnd_5308577 := by
    simpa [prefixWord, tailWord_5308577, baseEnd_5308577] using wordTrace_append hprefix tailTrace_5308577
  have hstable : (prefixWord ++ tailWord_5308577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308577).length < 2 ^ (prefixWord ++ tailWord_5308577).sum := by decide
  have hdescent : baseEnd_5308577 < baseStart_5308577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308600 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 1, 4, 2]
def baseStart_5308600 : Nat := 118140960795 + 5308600 * 2 ^ 59
def prefixEnd_5308600 : Nat := 4983230072969 + 3 ^ 40 * 5308600 * 2
def baseEnd_5308600 : Nat := 2725863402458035311786199

theorem tailTrace_5308600 : CollatzResearch.WordTrace tailWord_5308600 prefixEnd_5308600 2725863402458035311786199 := by
  unfold tailWord_5308600
  simp only [CollatzResearch.WordTrace]
  refine ⟨96810274283928155772037627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129080365711904207696050169 96810274283928155772037627)
  ·
    refine ⟨145215411425892233658056441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96810274283928155772037627 145215411425892233658056441)
    ·
      refine ⟨108911558569419175243542331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145215411425892233658056441 108911558569419175243542331)
      ·
        refine ⟨163367337854128762865313497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108911558569419175243542331 163367337854128762865313497)
        ·
          refine ⟨122525503390596572148985123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163367337854128762865313497 122525503390596572148985123)
          ·
            refine ⟨183788255085894858223477685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122525503390596572148985123 183788255085894858223477685)
            ·
              refine ⟨17230148914302642958451033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 183788255085894858223477685 17230148914302642958451033)
              ·
                refine ⟨12922611685726982218838275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17230148914302642958451033 12922611685726982218838275)
                ·
                  refine ⟨19383917528590473328257413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12922611685726982218838275 19383917528590473328257413)
                  ·
                    refine ⟨3634484536610713749048265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19383917528590473328257413 3634484536610713749048265)
                    ·
                      refine ⟨2725863402458035311786199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3634484536610713749048265 2725863402458035311786199)
                      ·
                        rfl

theorem cell23_5308600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 1, 4, 2].length) (baseStart_5308600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308600 prefixEnd_5308600 := by exact prefixLift 5308600
  have htrace : WordTrace (prefixWord ++ tailWord_5308600) baseStart_5308600 baseEnd_5308600 := by
    simpa [prefixWord, tailWord_5308600, baseEnd_5308600] using wordTrace_append hprefix tailTrace_5308600
  have hstable : (prefixWord ++ tailWord_5308600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308600).length < 2 ^ (prefixWord ++ tailWord_5308600).sum := by decide
  have hdescent : baseEnd_5308600 < baseStart_5308600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308633 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 1, 5, 3]
def baseStart_5308633 : Nat := 118140960795 + 5308633 * 2 ^ 59
def prefixEnd_5308633 : Nat := 4983230072969 + 3 ^ 40 * 5308633 * 2
def baseEnd_5308633 : Nat := 2725880347319633682673547

theorem tailTrace_5308633 : CollatzResearch.WordTrace tailWord_5308633 prefixEnd_5308633 2725880347319633682673547 := by
  unfold tailWord_5308633
  simp only [CollatzResearch.WordTrace]
  refine ⟨193621752176736758180026553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129081168117824505453351035 193621752176736758180026553)
  ·
    refine ⟨145216314132552568635019915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193621752176736758180026553 145216314132552568635019915)
    ·
      refine ⟨217824471198828852952529873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145216314132552568635019915 217824471198828852952529873)
      ·
        refine ⟨163368353399121639714397405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217824471198828852952529873 163368353399121639714397405)
        ·
          refine ⟨61263132524670614892899027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163368353399121639714397405 61263132524670614892899027)
          ·
            refine ⟨91894698787005922339348541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61263132524670614892899027 91894698787005922339348541)
            ·
              refine ⟨34460512045127220877255703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91894698787005922339348541 34460512045127220877255703)
              ·
                refine ⟨51690768067690831315883555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34460512045127220877255703 51690768067690831315883555)
                ·
                  refine ⟨77536152101536246973825333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51690768067690831315883555 77536152101536246973825333)
                  ·
                    refine ⟨7269014259519023153796125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77536152101536246973825333 7269014259519023153796125)
                    ·
                      refine ⟨2725880347319633682673547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7269014259519023153796125 2725880347319633682673547)
                      ·
                        rfl

theorem cell23_5308633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_5308633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308633 prefixEnd_5308633 := by exact prefixLift 5308633
  have htrace : WordTrace (prefixWord ++ tailWord_5308633) baseStart_5308633 baseEnd_5308633 := by
    simpa [prefixWord, tailWord_5308633, baseEnd_5308633] using wordTrace_append hprefix tailTrace_5308633
  have hstable : (prefixWord ++ tailWord_5308633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308633).length < 2 ^ (prefixWord ++ tailWord_5308633).sum := by decide
  have hdescent : baseEnd_5308633 < baseStart_5308633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308670 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_5308670 : Nat := 118140960795 + 5308670 * 2 ^ 59
def prefixEnd_5308670 : Nat := 4983230072969 + 3 ^ 40 * 5308670 * 2
def baseEnd_5308670 : Nat := 908633115367950012636959

theorem tailTrace_5308670 : CollatzResearch.WordTrace tailWord_5308670 prefixEnd_5308670 908633115367950012636959 := by
  unfold tailWord_5308670
  simp only [CollatzResearch.WordTrace]
  refine ⟨24202887709700339187390433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129082067785068475666082309 24202887709700339187390433)
  ·
    refine ⟨18152165782275254390542825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24202887709700339187390433 18152165782275254390542825)
    ·
      refine ⟨13614124336706440792907119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18152165782275254390542825 13614124336706440792907119)
      ·
        refine ⟨20421186505059661189360679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13614124336706440792907119 20421186505059661189360679)
        ·
          refine ⟨30631779757589491784041019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20421186505059661189360679 30631779757589491784041019)
          ·
            refine ⟨45947669636384237676061529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30631779757589491784041019 45947669636384237676061529)
            ·
              refine ⟨34460752227288178257046147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45947669636384237676061529 34460752227288178257046147)
              ·
                refine ⟨51691128340932267385569221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34460752227288178257046147 51691128340932267385569221)
                ·
                  refine ⟨9692086563924800134794229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51691128340932267385569221 9692086563924800134794229)
                  ·
                    refine ⟨908633115367950012636959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9692086563924800134794229 908633115367950012636959)
                    ·
                      rfl

theorem cell23_5308670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_5308670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308670 prefixEnd_5308670 := by exact prefixLift 5308670
  have htrace : WordTrace (prefixWord ++ tailWord_5308670) baseStart_5308670 baseEnd_5308670 := by
    simpa [prefixWord, tailWord_5308670, baseEnd_5308670] using wordTrace_append hprefix tailTrace_5308670
  have hstable : (prefixWord ++ tailWord_5308670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308670).length < 2 ^ (prefixWord ++ tailWord_5308670).sum := by decide
  have hdescent : baseEnd_5308670 < baseStart_5308670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308734 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_5308734 : Nat := 118140960795 + 5308734 * 2 ^ 59
def prefixEnd_5308734 : Nat := 4983230072969 + 3 ^ 40 * 5308734 * 2
def baseEnd_5308734 : Nat := 908644069621912595836861

theorem tailTrace_5308734 : CollatzResearch.WordTrace tailWord_5308734 prefixEnd_5308734 908644069621912595836861 := by
  unfold tailWord_5308734
  simp only [CollatzResearch.WordTrace]
  refine ⟨24203179493671356553681657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129083623966247234952968837 24203179493671356553681657)
  ·
    refine ⟨18152384620253517415261243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24203179493671356553681657 18152384620253517415261243)
    ·
      refine ⟨27228576930380276122891865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18152384620253517415261243 27228576930380276122891865)
      ·
        refine ⟨20421432697785207092168899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27228576930380276122891865 20421432697785207092168899)
        ·
          refine ⟨30632149046677810638253349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20421432697785207092168899 30632149046677810638253349)
          ·
            refine ⟨5743527946252089494672503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30632149046677810638253349 5743527946252089494672503)
            ·
              refine ⟨8615291919378134242008755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5743527946252089494672503 8615291919378134242008755)
              ·
                refine ⟨12922937879067201363013133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8615291919378134242008755 12922937879067201363013133)
                ·
                  refine ⟨4846101704650200511129925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12922937879067201363013133 4846101704650200511129925)
                  ·
                    refine ⟨908644069621912595836861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4846101704650200511129925 908644069621912595836861)
                    ·
                      rfl

theorem cell23_5308734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_5308734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308734 prefixEnd_5308734 := by exact prefixLift 5308734
  have htrace : WordTrace (prefixWord ++ tailWord_5308734) baseStart_5308734 baseEnd_5308734 := by
    simpa [prefixWord, tailWord_5308734, baseEnd_5308734] using wordTrace_append hprefix tailTrace_5308734
  have hstable : (prefixWord ++ tailWord_5308734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308734).length < 2 ^ (prefixWord ++ tailWord_5308734).sum := by decide
  have hdescent : baseEnd_5308734 < baseStart_5308734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308760 : List Nat := [2, 1, 2, 2, 1, 1, 2, 6, 1, 5]
def baseStart_5308760 : Nat := 118140960795 + 5308760 * 2 ^ 59
def prefixEnd_5308760 : Nat := 4983230072969 + 3 ^ 40 * 5308760 * 2
def baseEnd_5308760 : Nat := 908648519787584895261821

theorem tailTrace_5308760 : CollatzResearch.WordTrace tailWord_5308760 prefixEnd_5308760 908648519787584895261821 := by
  unfold tailWord_5308760
  simp only [CollatzResearch.WordTrace]
  refine ⟨96813192123638329434949867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129084256164851105913266489 96813192123638329434949867)
  ·
    refine ⟨145219788185457494152424801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96813192123638329434949867 145219788185457494152424801)
    ·
      refine ⟨108914841139093120614318601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145219788185457494152424801 108914841139093120614318601)
      ·
        refine ⟨81686130854319840460738951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108914841139093120614318601 81686130854319840460738951)
        ·
          refine ⟨122529196281479760691108427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81686130854319840460738951 122529196281479760691108427)
          ·
            refine ⟨183793794422219641036662641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122529196281479760691108427 183793794422219641036662641)
            ·
              refine ⟨137845345816664730777496981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183793794422219641036662641 137845345816664730777496981)
              ·
                refine ⟨6461500585156159255195171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 137845345816664730777496981 6461500585156159255195171)
                ·
                  refine ⟨9692250877734238882792757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6461500585156159255195171 9692250877734238882792757)
                  ·
                    refine ⟨908648519787584895261821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9692250877734238882792757 908648519787584895261821)
                    ·
                      rfl

theorem cell23_5308760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 1, 5].length) (baseStart_5308760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308760 prefixEnd_5308760 := by exact prefixLift 5308760
  have htrace : WordTrace (prefixWord ++ tailWord_5308760) baseStart_5308760 baseEnd_5308760 := by
    simpa [prefixWord, tailWord_5308760, baseEnd_5308760] using wordTrace_append hprefix tailTrace_5308760
  have hstable : (prefixWord ++ tailWord_5308760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308760).length < 2 ^ (prefixWord ++ tailWord_5308760).sum := by decide
  have hdescent : baseEnd_5308760 < baseStart_5308760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308767 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 2, 3, 2]
def baseStart_5308767 : Nat := 118140960795 + 5308767 * 2 ^ 59
def prefixEnd_5308767 : Nat := 4983230072969 + 3 ^ 40 * 5308767 * 2
def baseEnd_5308767 : Nat := 2725949153727336158397931

theorem tailTrace_5308767 : CollatzResearch.WordTrace tailWord_5308767 prefixEnd_5308767 2725949153727336158397931 := by
  unfold tailWord_5308767
  simp only [CollatzResearch.WordTrace]
  refine ⟨193626639558251299065404555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129084426372167532710269703 193626639558251299065404555)
  ·
    refine ⟨290439959337376948598106833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193626639558251299065404555 290439959337376948598106833)
    ·
      refine ⟨217829969503032711448580125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290439959337376948598106833 217829969503032711448580125)
      ·
        refine ⟨81686238563637266793217547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217829969503032711448580125 81686238563637266793217547)
        ·
          refine ⟨122529357845455900189826321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81686238563637266793217547 122529357845455900189826321)
          ·
            refine ⟨91897018384091925142369741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122529357845455900189826321 91897018384091925142369741)
            ·
              refine ⟨34461381894034471928388653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91897018384091925142369741 34461381894034471928388653)
              ·
                refine ⟨12923018210262926973145745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34461381894034471928388653 12923018210262926973145745)
                ·
                  refine ⟨9692263657697195229859309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12923018210262926973145745 9692263657697195229859309)
                  ·
                    refine ⟨3634598871636448211197241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9692263657697195229859309 3634598871636448211197241)
                    ·
                      refine ⟨2725949153727336158397931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3634598871636448211197241 2725949153727336158397931)
                      ·
                        rfl

theorem cell23_5308767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_5308767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308767 prefixEnd_5308767 := by exact prefixLift 5308767
  have htrace : WordTrace (prefixWord ++ tailWord_5308767) baseStart_5308767 baseEnd_5308767 := by
    simpa [prefixWord, tailWord_5308767, baseEnd_5308767] using wordTrace_append hprefix tailTrace_5308767
  have hstable : (prefixWord ++ tailWord_5308767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308767).length < 2 ^ (prefixWord ++ tailWord_5308767).sum := by decide
  have hdescent : baseEnd_5308767 < baseStart_5308767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308777 : List Nat := [1, 2, 1, 1, 1, 3, 7, 1, 1, 5]
def baseStart_5308777 : Nat := 118140960795 + 5308777 * 2 ^ 59
def prefixEnd_5308777 : Nat := 4983230072969 + 3 ^ 40 * 5308777 * 2
def baseEnd_5308777 : Nat := 908651429511293706424295

theorem tailTrace_5308777 : CollatzResearch.WordTrace tailWord_5308777 prefixEnd_5308777 908651429511293706424295 := by
  unfold tailWord_5308777
  simp only [CollatzResearch.WordTrace]
  refine ⟨193627004288215070773268585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129084669525476713848845723 193627004288215070773268585)
  ·
    refine ⟨145220253216161303079951439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193627004288215070773268585 145220253216161303079951439)
    ·
      refine ⟨217830379824241954619927159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145220253216161303079951439 217830379824241954619927159)
      ·
        refine ⟨326745569736362931929890739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217830379824241954619927159 326745569736362931929890739)
        ·
          refine ⟨490118354604544397894836109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326745569736362931929890739 490118354604544397894836109)
          ·
            refine ⟨183794382976704149210563541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 490118354604544397894836109 183794382976704149210563541)
            ·
              refine ⟨4307680851016503497122583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 183794382976704149210563541 4307680851016503497122583)
              ·
                refine ⟨6461521276524755245683875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4307680851016503497122583 6461521276524755245683875)
                ·
                  refine ⟨9692281914787132868525813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6461521276524755245683875 9692281914787132868525813)
                  ·
                    refine ⟨908651429511293706424295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9692281914787132868525813 908651429511293706424295)
                    ·
                      rfl

theorem cell23_5308777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 1, 5].length) (baseStart_5308777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308777 prefixEnd_5308777 := by exact prefixLift 5308777
  have htrace : WordTrace (prefixWord ++ tailWord_5308777) baseStart_5308777 baseEnd_5308777 := by
    simpa [prefixWord, tailWord_5308777, baseEnd_5308777] using wordTrace_append hprefix tailTrace_5308777
  have hstable : (prefixWord ++ tailWord_5308777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308777).length < 2 ^ (prefixWord ++ tailWord_5308777).sum := by decide
  have hdescent : baseEnd_5308777 < baseStart_5308777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308807 : List Nat := [1, 1, 4, 2, 2, 1, 1, 5, 2, 4]
def baseStart_5308807 : Nat := 118140960795 + 5308807 * 2 ^ 59
def prefixEnd_5308807 : Nat := 4983230072969 + 3 ^ 40 * 5308807 * 2
def baseEnd_5308807 : Nat := 908656564317838667299249

theorem tailTrace_5308807 : CollatzResearch.WordTrace tailWord_5308807 prefixEnd_5308807 908656564317838667299249 := by
  unfold tailWord_5308807
  simp only [CollatzResearch.WordTrace]
  refine ⟨193628098478106385896860675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129085398985404257264573783 193628098478106385896860675)
  ·
    refine ⟨290442147717159578845291013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193628098478106385896860675 290442147717159578845291013)
    ·
      refine ⟨54457902696967421033492065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290442147717159578845291013 54457902696967421033492065)
      ·
        refine ⟨40843427022725565775119049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54457902696967421033492065 40843427022725565775119049)
        ·
          refine ⟨30632570267044174331339287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40843427022725565775119049 30632570267044174331339287)
          ·
            refine ⟨45948855400566261497008931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30632570267044174331339287 45948855400566261497008931)
            ·
              refine ⟨68923283100849392245513397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45948855400566261497008931 68923283100849392245513397)
              ·
                refine ⟨6461557790704630523016881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68923283100849392245513397 6461557790704630523016881)
                ·
                  refine ⟨4846168343028472892262661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6461557790704630523016881 4846168343028472892262661)
                  ·
                    refine ⟨908656564317838667299249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4846168343028472892262661 908656564317838667299249)
                    ·
                      rfl

theorem cell23_5308807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_5308807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308807 prefixEnd_5308807 := by exact prefixLift 5308807
  have htrace : WordTrace (prefixWord ++ tailWord_5308807) baseStart_5308807 baseEnd_5308807 := by
    simpa [prefixWord, tailWord_5308807, baseEnd_5308807] using wordTrace_append hprefix tailTrace_5308807
  have hstable : (prefixWord ++ tailWord_5308807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308807).length < 2 ^ (prefixWord ++ tailWord_5308807).sum := by decide
  have hdescent : baseEnd_5308807 < baseStart_5308807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308834 : List Nat := [3, 3, 1, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_5308834 : Nat := 118140960795 + 5308834 * 2 ^ 59
def prefixEnd_5308834 : Nat := 4983230072969 + 3 ^ 40 * 5308834 * 2
def baseEnd_5308834 : Nat := 2725983556931187396260123

theorem tailTrace_5308834 : CollatzResearch.WordTrace tailWord_5308834 prefixEnd_5308834 2725983556931187396260123 := by
  unfold tailWord_5308834
  simp only [CollatzResearch.WordTrace]
  refine ⟨48407270812252142377023389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129086055499339046338729037 48407270812252142377023389)
  ·
    refine ⟨18152726554594553391383771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48407270812252142377023389 18152726554594553391383771)
    ·
      refine ⟨27229089831891830087075657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18152726554594553391383771 27229089831891830087075657)
      ·
        refine ⟨20421817373918872565306743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27229089831891830087075657 20421817373918872565306743)
        ·
          refine ⟨30632726060878308847960115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20421817373918872565306743 30632726060878308847960115)
          ·
            refine ⟨45949089091317463271940173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30632726060878308847960115 45949089091317463271940173)
            ·
              refine ⟨17230908409244048726977565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45949089091317463271940173 17230908409244048726977565)
              ·
                refine ⟨6461590653466518272616587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17230908409244048726977565 6461590653466518272616587)
                ·
                  refine ⟨9692385980199777408924881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6461590653466518272616587 9692385980199777408924881)
                  ·
                    refine ⟨7269289485149833056693661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9692385980199777408924881 7269289485149833056693661)
                    ·
                      refine ⟨2725983556931187396260123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7269289485149833056693661 2725983556931187396260123)
                      ·
                        rfl

theorem cell23_5308834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_5308834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308834 prefixEnd_5308834 := by exact prefixLift 5308834
  have htrace : WordTrace (prefixWord ++ tailWord_5308834) baseStart_5308834 baseEnd_5308834 := by
    simpa [prefixWord, tailWord_5308834, baseEnd_5308834] using wordTrace_append hprefix tailTrace_5308834
  have hstable : (prefixWord ++ tailWord_5308834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308834).length < 2 ^ (prefixWord ++ tailWord_5308834).sum := by decide
  have hdescent : baseEnd_5308834 < baseStart_5308834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308882 : List Nat := [3, 2, 2, 4, 1, 2, 1, 3, 1, 2, 2]
def baseStart_5308882 : Nat := 118140960795 + 5308882 * 2 ^ 59
def prefixEnd_5308882 : Nat := 4983230072969 + 3 ^ 40 * 5308882 * 2
def baseEnd_5308882 : Nat := 2726008204002603208459903

theorem tailTrace_5308882 : CollatzResearch.WordTrace tailWord_5308882 prefixEnd_5308882 2726008204002603208459903 := by
  unfold tailWord_5308882
  simp only [CollatzResearch.WordTrace]
  refine ⟨48407708488208668426460225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129087222635223115803893933 48407708488208668426460225)
  ·
    refine ⟨36305781366156501319845169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48407708488208668426460225 36305781366156501319845169)
    ·
      refine ⟨27229336024617375989883877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36305781366156501319845169 27229336024617375989883877)
      ·
        refine ⟨5105500504615757998103227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27229336024617375989883877 5105500504615757998103227)
        ·
          refine ⟨7658250756923636997154841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5105500504615757998103227 7658250756923636997154841)
          ·
            refine ⟨5743688067692727747866131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7658250756923636997154841 5743688067692727747866131)
            ·
              refine ⟨8615532101539091621799197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5743688067692727747866131 8615532101539091621799197)
              ·
                refine ⟨3230824538077159358174699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8615532101539091621799197 3230824538077159358174699)
                ·
                  refine ⟨4846236807115739037262049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3230824538077159358174699 4846236807115739037262049)
                  ·
                    refine ⟨3634677605336804277946537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4846236807115739037262049 3634677605336804277946537)
                    ·
                      refine ⟨2726008204002603208459903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3634677605336804277946537 2726008204002603208459903)
                      ·
                        rfl

theorem cell23_5308882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_5308882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308882 prefixEnd_5308882 := by exact prefixLift 5308882
  have htrace : WordTrace (prefixWord ++ tailWord_5308882) baseStart_5308882 baseEnd_5308882 := by
    simpa [prefixWord, tailWord_5308882, baseEnd_5308882] using wordTrace_append hprefix tailTrace_5308882
  have hstable : (prefixWord ++ tailWord_5308882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308882).length < 2 ^ (prefixWord ++ tailWord_5308882).sum := by decide
  have hdescent : baseEnd_5308882 < baseStart_5308882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308941 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_5308941 : Nat := 118140960795 + 5308941 * 2 ^ 59
def prefixEnd_5308941 : Nat := 4983230072969 + 3 ^ 40 * 5308941 * 2
def baseEnd_5308941 : Nat := 2726038499361218477622131

theorem tailTrace_5308941 : CollatzResearch.WordTrace tailWord_5308941 prefixEnd_5308941 2726038499361218477622131 := by
  unfold tailWord_5308941
  simp only [CollatzResearch.WordTrace]
  refine ⟨193632985859620926782238677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129088657239747284521492451 193632985859620926782238677)
  ·
    refine ⟨4538273106084865471458719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 193632985859620926782238677 4538273106084865471458719)
    ·
      refine ⟨6807409659127298207188079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4538273106084865471458719 6807409659127298207188079)
      ·
        refine ⟨10211114488690947310782119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6807409659127298207188079 10211114488690947310782119)
        ·
          refine ⟨15316671733036420966173179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10211114488690947310782119 15316671733036420966173179)
          ·
            refine ⟨22975007599554631449259769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15316671733036420966173179 22975007599554631449259769)
            ·
              refine ⟨17231255699665973586944827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22975007599554631449259769 17231255699665973586944827)
              ·
                refine ⟨25846883549498960380417241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17231255699665973586944827 25846883549498960380417241)
                ·
                  refine ⟨19385162662124220285312931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25846883549498960380417241 19385162662124220285312931)
                  ·
                    refine ⟨29077743993186330427969397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19385162662124220285312931 29077743993186330427969397)
                    ·
                      refine ⟨2726038499361218477622131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29077743993186330427969397 2726038499361218477622131)
                      ·
                        rfl

theorem cell23_5308941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_5308941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308941 prefixEnd_5308941 := by exact prefixLift 5308941
  have htrace : WordTrace (prefixWord ++ tailWord_5308941) baseStart_5308941 baseEnd_5308941 := by
    simpa [prefixWord, tailWord_5308941, baseEnd_5308941] using wordTrace_append hprefix tailTrace_5308941
  have hstable : (prefixWord ++ tailWord_5308941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308941).length < 2 ^ (prefixWord ++ tailWord_5308941).sum := by decide
  have hdescent : baseEnd_5308941 < baseStart_5308941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5308977 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 4, 1, 4]
def baseStart_5308977 : Nat := 118140960795 + 5308977 * 2 ^ 59
def prefixEnd_5308977 : Nat := 4983230072969 + 3 ^ 40 * 5308977 * 2
def baseEnd_5308977 : Nat := 2726056984664780336771965

theorem tailTrace_5308977 : CollatzResearch.WordTrace tailWord_5308977 prefixEnd_5308977 2726056984664780336771965 := by
  unfold tailWord_5308977
  simp only [CollatzResearch.WordTrace]
  refine ⟨193634298887490504930549185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129089532591660336620366123 193634298887490504930549185)
  ·
    refine ⟨145225724165617878697911889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193634298887490504930549185 145225724165617878697911889)
    ·
      refine ⟨108919293124213409023433917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145225724165617878697911889 108919293124213409023433917)
      ·
        refine ⟨40844734921580028383787719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108919293124213409023433917 40844734921580028383787719)
        ·
          refine ⟨61267102382370042575681579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40844734921580028383787719 61267102382370042575681579)
          ·
            refine ⟨91900653573555063863522369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61267102382370042575681579 91900653573555063863522369)
            ·
              refine ⟨68925490180166297897641777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91900653573555063863522369 68925490180166297897641777)
              ·
                refine ⟨51694117635124723423231333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68925490180166297897641777 51694117635124723423231333)
                ·
                  refine ⟨9692647056585885641855875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51694117635124723423231333 9692647056585885641855875)
                  ·
                    refine ⟨14538970584878828462783813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9692647056585885641855875 14538970584878828462783813)
                    ·
                      refine ⟨2726056984664780336771965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14538970584878828462783813 2726056984664780336771965)
                      ·
                        rfl

theorem cell23_5308977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_5308977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5308977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5308977 prefixEnd_5308977 := by exact prefixLift 5308977
  have htrace : WordTrace (prefixWord ++ tailWord_5308977) baseStart_5308977 baseEnd_5308977 := by
    simpa [prefixWord, tailWord_5308977, baseEnd_5308977] using wordTrace_append hprefix tailTrace_5308977
  have hstable : (prefixWord ++ tailWord_5308977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5308977).length < 2 ^ (prefixWord ++ tailWord_5308977).sum := by decide
  have hdescent : baseEnd_5308977 < baseStart_5308977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5308977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309047 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 3, 5]
def baseStart_5309047 : Nat := 118140960795 + 5309047 * 2 ^ 59
def prefixEnd_5309047 : Nat := 4983230072969 + 3 ^ 40 * 5309047 * 2
def baseEnd_5309047 : Nat := 908697642770198354298881

theorem tailTrace_5309047 : CollatzResearch.WordTrace tailWord_5309047 prefixEnd_5309047 908697642770198354298881 := by
  unfold tailWord_5309047
  simp only [CollatzResearch.WordTrace]
  refine ⟨193636851997236906885597395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129091234664824604590398263 193636851997236906885597395)
  ·
    refine ⟨290455277995855360328396093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193636851997236906885597395 290455277995855360328396093)
    ·
      refine ⟨108920729248445760123148535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290455277995855360328396093 108920729248445760123148535)
      ·
        refine ⟨163381093872668640184722803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108920729248445760123148535 163381093872668640184722803)
        ·
          refine ⟨245071640809002960277084205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163381093872668640184722803 245071640809002960277084205)
          ·
            refine ⟨91901865303376110103906577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245071640809002960277084205 91901865303376110103906577)
            ·
              refine ⟨68926398977532082577929933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91901865303376110103906577 68926398977532082577929933)
              ·
                refine ⟨25847399616574530966723725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68926398977532082577929933 25847399616574530966723725)
                ·
                  refine ⟨9692774856215449112521397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25847399616574530966723725 9692774856215449112521397)
                  ·
                    refine ⟨908697642770198354298881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9692774856215449112521397 908697642770198354298881)
                    ·
                      rfl

theorem cell23_5309047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 5].length) (baseStart_5309047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309047 prefixEnd_5309047 := by exact prefixLift 5309047
  have htrace : WordTrace (prefixWord ++ tailWord_5309047) baseStart_5309047 baseEnd_5309047 := by
    simpa [prefixWord, tailWord_5309047, baseEnd_5309047] using wordTrace_append hprefix tailTrace_5309047
  have hstable : (prefixWord ++ tailWord_5309047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309047).length < 2 ^ (prefixWord ++ tailWord_5309047).sum := by decide
  have hdescent : baseEnd_5309047 < baseStart_5309047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309098 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 3, 5]
def baseStart_5309098 : Nat := 118140960795 + 5309098 * 2 ^ 59
def prefixEnd_5309098 : Nat := 4983230072969 + 3 ^ 40 * 5309098 * 2
def baseEnd_5309098 : Nat := 908706371941324787786303

theorem tailTrace_5309098 : CollatzResearch.WordTrace tailWord_5309098 prefixEnd_5309098 908706371941324787786303 := by
  unfold tailWord_5309098
  simp only [CollatzResearch.WordTrace]
  refine ⟨48409678030013035648925987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129092474746701428397135965 48409678030013035648925987)
  ·
    refine ⟨72614517045019553473388981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48409678030013035648925987 72614517045019553473388981)
    ·
      refine ⟨6807610972970583138130217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72614517045019553473388981 6807610972970583138130217)
      ·
        refine ⟨5105708229727937353597663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6807610972970583138130217 5105708229727937353597663)
        ·
          refine ⟨7658562344591906030396495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5105708229727937353597663 7658562344591906030396495)
          ·
            refine ⟨11487843516887859045594743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7658562344591906030396495 11487843516887859045594743)
            ·
              refine ⟨17231765275331788568392115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11487843516887859045594743 17231765275331788568392115)
              ·
                refine ⟨25847647912997682852588173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17231765275331788568392115 25847647912997682852588173)
                ·
                  refine ⟨9692867967374131069720565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25847647912997682852588173 9692867967374131069720565)
                  ·
                    refine ⟨908706371941324787786303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9692867967374131069720565 908706371941324787786303)
                    ·
                      rfl

theorem cell23_5309098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_5309098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309098 prefixEnd_5309098 := by exact prefixLift 5309098
  have htrace : WordTrace (prefixWord ++ tailWord_5309098) baseStart_5309098 baseEnd_5309098 := by
    simpa [prefixWord, tailWord_5309098, baseEnd_5309098] using wordTrace_append hprefix tailTrace_5309098
  have hstable : (prefixWord ++ tailWord_5309098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309098).length < 2 ^ (prefixWord ++ tailWord_5309098).sum := by decide
  have hdescent : baseEnd_5309098 < baseStart_5309098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309101 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_5309101 : Nat := 118140960795 + 5309101 * 2 ^ 59
def prefixEnd_5309101 : Nat := 4983230072969 + 3 ^ 40 * 5309101 * 2
def baseEnd_5309101 : Nat := 2726120656265937851621395

theorem tailTrace_5309101 : CollatzResearch.WordTrace tailWord_5309101 prefixEnd_5309101 2726120656265937851621395 := by
  unfold tailWord_5309101
  simp only [CollatzResearch.WordTrace]
  refine ⟨193638821539041274108063157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129092547692694182738708771 193638821539041274108063157)
  ·
    refine ⟨18153639519285119447630921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193638821539041274108063157 18153639519285119447630921)
    ·
      refine ⟨13615229639463839585723191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18153639519285119447630921 13615229639463839585723191)
      ·
        refine ⟨20422844459195759378584787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13615229639463839585723191 20422844459195759378584787)
        ·
          refine ⟨30634266688793639067877181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20422844459195759378584787 30634266688793639067877181)
          ·
            refine ⟨11487850008297614650453943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30634266688793639067877181 11487850008297614650453943)
            ·
              refine ⟨17231775012446421975680915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11487850008297614650453943 17231775012446421975680915)
              ·
                refine ⟨25847662518669632963521373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17231775012446421975680915 25847662518669632963521373)
                ·
                  refine ⟨9692873444501112361320515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25847662518669632963521373 9692873444501112361320515)
                  ·
                    refine ⟨14539310166751668541980773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9692873444501112361320515 14539310166751668541980773)
                    ·
                      refine ⟨2726120656265937851621395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14539310166751668541980773 2726120656265937851621395)
                      ·
                        rfl

theorem cell23_5309101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_5309101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309101 prefixEnd_5309101 := by exact prefixLift 5309101
  have htrace : WordTrace (prefixWord ++ tailWord_5309101) baseStart_5309101 baseEnd_5309101 := by
    simpa [prefixWord, tailWord_5309101, baseEnd_5309101] using wordTrace_append hprefix tailTrace_5309101
  have hstable : (prefixWord ++ tailWord_5309101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309101).length < 2 ^ (prefixWord ++ tailWord_5309101).sum := by decide
  have hdescent : baseEnd_5309101 < baseStart_5309101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309105 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 2, 3, 2]
def baseStart_5309105 : Nat := 118140960795 + 5309105 * 2 ^ 59
def prefixEnd_5309105 : Nat := 4983230072969 + 3 ^ 40 * 5309105 * 2
def baseEnd_5309105 : Nat := 2726122710188555835971377

theorem tailTrace_5309105 : CollatzResearch.WordTrace tailWord_5309105 prefixEnd_5309105 2726122710188555835971377 := by
  unfold tailWord_5309105
  simp only [CollatzResearch.WordTrace]
  refine ⟨193638967431026782791208769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129092644954017855194139179 193638967431026782791208769)
  ·
    refine ⟨145229225573270087093406577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193638967431026782791208769 145229225573270087093406577)
    ·
      refine ⟨108921919179952565320054933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145229225573270087093406577 108921919179952565320054933)
      ·
        refine ⟨5105714961560276499377575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108921919179952565320054933 5105714961560276499377575)
        ·
          refine ⟨7658572442340414749066363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5105714961560276499377575 7658572442340414749066363)
          ·
            refine ⟨11487858663510622123599545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7658572442340414749066363 11487858663510622123599545)
            ·
              refine ⟨8615893997632966592699659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11487858663510622123599545 8615893997632966592699659)
              ·
                refine ⟨12923840996449449889049489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8615893997632966592699659 12923840996449449889049489)
                ·
                  refine ⟨9692880747337087416787117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12923840996449449889049489 9692880747337087416787117)
                  ·
                    refine ⟨3634830280251407781295169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9692880747337087416787117 3634830280251407781295169)
                    ·
                      refine ⟨2726122710188555835971377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3634830280251407781295169 2726122710188555835971377)
                      ·
                        rfl

theorem cell23_5309105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_5309105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309105 prefixEnd_5309105 := by exact prefixLift 5309105
  have htrace : WordTrace (prefixWord ++ tailWord_5309105) baseStart_5309105 baseEnd_5309105 := by
    simpa [prefixWord, tailWord_5309105, baseEnd_5309105] using wordTrace_append hprefix tailTrace_5309105
  have hstable : (prefixWord ++ tailWord_5309105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309105).length < 2 ^ (prefixWord ++ tailWord_5309105).sum := by decide
  have hdescent : baseEnd_5309105 < baseStart_5309105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309107 : List Nat := [1, 1, 1, 2, 3, 4, 2, 9]
def baseStart_5309107 : Nat := 118140960795 + 5309107 * 2 ^ 59
def prefixEnd_5309107 : Nat := 4983230072969 + 3 ^ 40 * 5309107 * 2
def baseEnd_5309107 : Nat := 100967545820365364005421

theorem tailTrace_5309107 : CollatzResearch.WordTrace tailWord_5309107 prefixEnd_5309107 100967545820365364005421 := by
  unfold tailWord_5309107
  simp only [CollatzResearch.WordTrace]
  refine ⟨193639040377019537132781575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129092693584679691421854383 193639040377019537132781575)
  ·
    refine ⟨290458560565529305699172363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193639040377019537132781575 290458560565529305699172363)
    ·
      refine ⟨435687840848293958548758545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290458560565529305699172363 435687840848293958548758545)
      ·
        refine ⟨326765880636220468911568909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435687840848293958548758545 326765880636220468911568909)
        ·
          refine ⟨122537205238582675841838341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326765880636220468911568909 122537205238582675841838341)
          ·
            refine ⟨22975725982234251720344689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122537205238582675841838341 22975725982234251720344689)
            ·
              refine ⟨17231794486675688790258517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22975725982234251720344689 17231794486675688790258517)
              ·
                refine ⟨100967545820365364005421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17231794486675688790258517 100967545820365364005421)
                ·
                  rfl

theorem cell23_5309107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 9].length) (baseStart_5309107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309107 prefixEnd_5309107 := by exact prefixLift 5309107
  have htrace : WordTrace (prefixWord ++ tailWord_5309107) baseStart_5309107 baseEnd_5309107 := by
    simpa [prefixWord, tailWord_5309107, baseEnd_5309107] using wordTrace_append hprefix tailTrace_5309107
  have hstable : (prefixWord ++ tailWord_5309107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309107).length < 2 ^ (prefixWord ++ tailWord_5309107).sum := by decide
  have hdescent : baseEnd_5309107 < baseStart_5309107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309114 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4]
def baseStart_5309114 : Nat := 118140960795 + 5309114 * 2 ^ 59
def prefixEnd_5309114 : Nat := 4983230072969 + 3 ^ 40 * 5309114 * 2
def baseEnd_5309114 : Nat := 2726127331514446300758835

theorem tailTrace_5309114 : CollatzResearch.WordTrace tailWord_5309114 prefixEnd_5309114 2726127331514446300758835 := by
  unfold tailWord_5309114
  simp only [CollatzResearch.WordTrace]
  refine ⟨48409823921998544332071599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129092863791996118218857597 48409823921998544332071599)
  ·
    refine ⟨72614735882997816498107399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48409823921998544332071599 72614735882997816498107399)
    ·
      refine ⟨108922103824496724747161099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72614735882997816498107399 108922103824496724747161099)
      ·
        refine ⟨163383155736745087120741649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108922103824496724747161099 163383155736745087120741649)
        ·
          refine ⟨122537366802558815340556237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163383155736745087120741649 122537366802558815340556237)
          ·
            refine ⟨45951512550959555752708589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122537366802558815340556237 45951512550959555752708589)
            ·
              refine ⟨17231817206609833407265721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45951512550959555752708589 17231817206609833407265721)
              ·
                refine ⟨12923862904957375055449291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17231817206609833407265721 12923862904957375055449291)
                ·
                  refine ⟨19385794357436062583173937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12923862904957375055449291 19385794357436062583173937)
                  ·
                    refine ⟨14539345768077046937380453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19385794357436062583173937 14539345768077046937380453)
                    ·
                      refine ⟨2726127331514446300758835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14539345768077046937380453 2726127331514446300758835)
                      ·
                        rfl

theorem cell23_5309114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_5309114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309114 prefixEnd_5309114 := by exact prefixLift 5309114
  have htrace : WordTrace (prefixWord ++ tailWord_5309114) baseStart_5309114 baseEnd_5309114 := by
    simpa [prefixWord, tailWord_5309114, baseEnd_5309114] using wordTrace_append hprefix tailTrace_5309114
  have hstable : (prefixWord ++ tailWord_5309114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309114).length < 2 ^ (prefixWord ++ tailWord_5309114).sum := by decide
  have hdescent : baseEnd_5309114 < baseStart_5309114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309118 : List Nat := [4, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4]
def baseStart_5309118 : Nat := 118140960795 + 5309118 * 2 ^ 59
def prefixEnd_5309118 : Nat := 4983230072969 + 3 ^ 40 * 5309118 * 2
def baseEnd_5309118 : Nat := 2726129385437064285108817

theorem tailTrace_5309118 : CollatzResearch.WordTrace tailWord_5309118 prefixEnd_5309118 2726129385437064285108817 := by
  unfold tailWord_5309118
  simp only [CollatzResearch.WordTrace]
  refine ⟨24204930197497460751429001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129092961053319790674288005 24204930197497460751429001)
  ·
    refine ⟨18153697648123095563571751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24204930197497460751429001 18153697648123095563571751)
    ·
      refine ⟨27230546472184643345357627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18153697648123095563571751 27230546472184643345357627)
      ·
        refine ⟨40845819708276965018036441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27230546472184643345357627 40845819708276965018036441)
        ·
          refine ⟨30634364781207723763527331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40845819708276965018036441 30634364781207723763527331)
          ·
            refine ⟨45951547171811585645290997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30634364781207723763527331 45951547171811585645290997)
            ·
              refine ⟨4307957547357336154246031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45951547171811585645290997 4307957547357336154246031)
              ·
                refine ⟨6461936321036004231369047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4307957547357336154246031 6461936321036004231369047)
                ·
                  refine ⟨9692904481554006347053571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6461936321036004231369047 9692904481554006347053571)
                  ·
                    refine ⟨14539356722331009520580357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9692904481554006347053571 14539356722331009520580357)
                    ·
                      refine ⟨2726129385437064285108817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14539356722331009520580357 2726129385437064285108817)
                      ·
                        rfl

theorem cell23_5309118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_5309118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309118 prefixEnd_5309118 := by exact prefixLift 5309118
  have htrace : WordTrace (prefixWord ++ tailWord_5309118) baseStart_5309118 baseEnd_5309118 := by
    simpa [prefixWord, tailWord_5309118, baseEnd_5309118] using wordTrace_append hprefix tailTrace_5309118
  have hstable : (prefixWord ++ tailWord_5309118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309118).length < 2 ^ (prefixWord ++ tailWord_5309118).sum := by decide
  have hdescent : baseEnd_5309118 < baseStart_5309118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309127 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_5309127 : Nat := 118140960795 + 5309127 * 2 ^ 59
def prefixEnd_5309127 : Nat := 4983230072969 + 3 ^ 40 * 5309127 * 2
def baseEnd_5309127 : Nat := 2726134006762954749896275

theorem tailTrace_5309127 : CollatzResearch.WordTrace tailWord_5309127 prefixEnd_5309127 2726134006762954749896275 := by
  unfold tailWord_5309127
  simp only [CollatzResearch.WordTrace]
  refine ⟨193639769836947080548509635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129093179891298053699006423 193639769836947080548509635)
  ·
    refine ⟨290459654755420620822764453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193639769836947080548509635 290459654755420620822764453)
    ·
      refine ⟨54461185266641366404268335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290459654755420620822764453 54461185266641366404268335)
      ·
        refine ⟨81691777899962049606402503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54461185266641366404268335 81691777899962049606402503)
        ·
          refine ⟨122537666849943074409603755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81691777899962049606402503 122537666849943074409603755)
          ·
            refine ⟨183806500274914611614405633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122537666849943074409603755 183806500274914611614405633)
            ·
              refine ⟨137854875206185958710804225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183806500274914611614405633 137854875206185958710804225)
              ·
                refine ⟨103391156404639469033103169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137854875206185958710804225 103391156404639469033103169)
                ·
                  refine ⟨77543367303479601774827377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103391156404639469033103169 77543367303479601774827377)
                  ·
                    refine ⟨58157525477609701331120533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77543367303479601774827377 58157525477609701331120533)
                    ·
                      refine ⟨2726134006762954749896275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58157525477609701331120533 2726134006762954749896275)
                      ·
                        rfl

theorem cell23_5309127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_5309127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309127 prefixEnd_5309127 := by exact prefixLift 5309127
  have htrace : WordTrace (prefixWord ++ tailWord_5309127) baseStart_5309127 baseEnd_5309127 := by
    simpa [prefixWord, tailWord_5309127, baseEnd_5309127] using wordTrace_append hprefix tailTrace_5309127
  have hstable : (prefixWord ++ tailWord_5309127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309127).length < 2 ^ (prefixWord ++ tailWord_5309127).sum := by decide
  have hdescent : baseEnd_5309127 < baseStart_5309127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309137 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 1, 9]
def baseStart_5309137 : Nat := 118140960795 + 5309137 * 2 ^ 59
def prefixEnd_5309137 : Nat := 4983230072969 + 3 ^ 40 * 5309137 * 2
def baseEnd_5309137 : Nat := 908713047189833236923743

theorem tailTrace_5309137 : CollatzResearch.WordTrace tailWord_5309137 prefixEnd_5309137 908713047189833236923743 := by
  unfold tailWord_5309137
  simp only [CollatzResearch.WordTrace]
  refine ⟨193640134566910852256373665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129093423044607234837582443 193640134566910852256373665)
  ·
    refine ⟨145230100925183139192280249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193640134566910852256373665 145230100925183139192280249)
    ·
      refine ⟨108922575693887354394210187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145230100925183139192280249 108922575693887354394210187)
      ·
        refine ⟨163383863540831031591315281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108922575693887354394210187 163383863540831031591315281)
        ·
          refine ⟨122537897655623273693486461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163383863540831031591315281 122537897655623273693486461)
          ·
            refine ⟨45951711620858727635057423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122537897655623273693486461 45951711620858727635057423)
            ·
              refine ⟨68927567431288091452586135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45951711620858727635057423 68927567431288091452586135)
              ·
                refine ⟨103391351146932137178879203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68927567431288091452586135 103391351146932137178879203)
                ·
                  refine ⟨155087026720398205768318805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103391351146932137178879203 155087026720398205768318805)
                  ·
                    refine ⟨908713047189833236923743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 155087026720398205768318805 908713047189833236923743)
                    ·
                      rfl

theorem cell23_5309137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_5309137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309137 prefixEnd_5309137 := by exact prefixLift 5309137
  have htrace : WordTrace (prefixWord ++ tailWord_5309137) baseStart_5309137 baseEnd_5309137 := by
    simpa [prefixWord, tailWord_5309137, baseEnd_5309137] using wordTrace_append hprefix tailTrace_5309137
  have hstable : (prefixWord ++ tailWord_5309137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309137).length < 2 ^ (prefixWord ++ tailWord_5309137).sum := by decide
  have hdescent : baseEnd_5309137 < baseStart_5309137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309147 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 5]
def baseStart_5309147 : Nat := 118140960795 + 5309147 * 2 ^ 59
def prefixEnd_5309147 : Nat := 4983230072969 + 3 ^ 40 * 5309147 * 2
def baseEnd_5309147 : Nat := 2726144276376044671646183

theorem tailTrace_5309147 : CollatzResearch.WordTrace tailWord_5309147 prefixEnd_5309147 2726144276376044671646183 := by
  unfold tailWord_5309147
  simp only [CollatzResearch.WordTrace]
  refine ⟨193640499296874623964237695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129093666197916415976158463 193640499296874623964237695)
  ·
    refine ⟨290460748945311935946356543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193640499296874623964237695 290460748945311935946356543)
    ·
      refine ⟨435691123417967903919534815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290460748945311935946356543 435691123417967903919534815)
      ·
        refine ⟨653536685126951855879302223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435691123417967903919534815 653536685126951855879302223)
        ·
          refine ⟨980305027690427783818953335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653536685126951855879302223 980305027690427783818953335)
          ·
            refine ⟨1470457541535641675728430003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980305027690427783818953335 1470457541535641675728430003)
            ·
              refine ⟨2205686312303462513592645005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470457541535641675728430003 2205686312303462513592645005)
              ·
                refine ⟨827132367113798442597241877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2205686312303462513592645005 827132367113798442597241877)
                ·
                  refine ⟨38771829708459301996745713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 827132367113798442597241877 38771829708459301996745713)
                  ·
                    refine ⟨29078872281344476497559285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38771829708459301996745713 29078872281344476497559285)
                    ·
                      refine ⟨2726144276376044671646183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29078872281344476497559285 2726144276376044671646183)
                      ·
                        rfl

theorem cell23_5309147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 5].length) (baseStart_5309147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309147 prefixEnd_5309147 := by exact prefixLift 5309147
  have htrace : WordTrace (prefixWord ++ tailWord_5309147) baseStart_5309147 baseEnd_5309147 := by
    simpa [prefixWord, tailWord_5309147, baseEnd_5309147] using wordTrace_append hprefix tailTrace_5309147
  have hstable : (prefixWord ++ tailWord_5309147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309147).length < 2 ^ (prefixWord ++ tailWord_5309147).sum := by decide
  have hdescent : baseEnd_5309147 < baseStart_5309147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309148 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_5309148 : Nat := 118140960795 + 5309148 * 2 ^ 59
def prefixEnd_5309148 : Nat := 4983230072969 + 3 ^ 40 * 5309148 * 2
def baseEnd_5309148 : Nat := 2726144789856699167733679

theorem tailTrace_5309148 : CollatzResearch.WordTrace tailWord_5309148 prefixEnd_5309148 2726144789856699167733679 := by
  unfold tailWord_5309148
  simp only [CollatzResearch.WordTrace]
  refine ⟨96820267884935500567512049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129093690513247334090016065 96820267884935500567512049)
  ·
    refine ⟨72615200913701625425634037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96820267884935500567512049 72615200913701625425634037)
    ·
      refine ⟨6807675085659527383653191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72615200913701625425634037 6807675085659527383653191)
      ·
        refine ⟨10211512628489291075479787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6807675085659527383653191 10211512628489291075479787)
        ·
          refine ⟨15317268942733936613219681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10211512628489291075479787 15317268942733936613219681)
          ·
            refine ⟨11487951707050452459914761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15317268942733936613219681 11487951707050452459914761)
            ·
              refine ⟨8615963780287839344936071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11487951707050452459914761 8615963780287839344936071)
              ·
                refine ⟨12923945670431759017404107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8615963780287839344936071 12923945670431759017404107)
                ·
                  refine ⟨19385918505647638526106161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12923945670431759017404107 19385918505647638526106161)
                  ·
                    refine ⟨14539438879235728894579621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19385918505647638526106161 14539438879235728894579621)
                    ·
                      refine ⟨2726144789856699167733679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14539438879235728894579621 2726144789856699167733679)
                      ·
                        rfl

theorem cell23_5309148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_5309148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309148 prefixEnd_5309148 := by exact prefixLift 5309148
  have htrace : WordTrace (prefixWord ++ tailWord_5309148) baseStart_5309148 baseEnd_5309148 := by
    simpa [prefixWord, tailWord_5309148, baseEnd_5309148] using wordTrace_append hprefix tailTrace_5309148
  have hstable : (prefixWord ++ tailWord_5309148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309148).length < 2 ^ (prefixWord ++ tailWord_5309148).sum := by decide
  have hdescent : baseEnd_5309148 < baseStart_5309148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309151 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 3]
def baseStart_5309151 : Nat := 118140960795 + 5309151 * 2 ^ 59
def prefixEnd_5309151 : Nat := 4983230072969 + 3 ^ 40 * 5309151 * 2
def baseEnd_5309151 : Nat := 2726146330298662655996165

theorem tailTrace_5309151 : CollatzResearch.WordTrace tailWord_5309151 prefixEnd_5309151 2726146330298662655996165 := by
  unfold tailWord_5309151
  simp only [CollatzResearch.WordTrace]
  refine ⟨193640645188860132647383307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129093763459240088431588871 193640645188860132647383307)
  ·
    refine ⟨290460967783290198971074961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193640645188860132647383307 290460967783290198971074961)
    ·
      refine ⟨217845725837467649228306221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290460967783290198971074961 217845725837467649228306221)
      ·
        refine ⟨81692147189050368460614833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217845725837467649228306221 81692147189050368460614833)
        ·
          refine ⟨61269110391787776345461125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81692147189050368460614833 61269110391787776345461125)
          ·
            refine ⟨11487958198460208064773961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61269110391787776345461125 11487958198460208064773961)
            ·
              refine ⟨8615968648845156048580471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11487958198460208064773961 8615968648845156048580471)
              ·
                refine ⟨12923952973267734072870707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8615968648845156048580471 12923952973267734072870707)
                ·
                  refine ⟨19385929459901601109306061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12923952973267734072870707 19385929459901601109306061)
                  ·
                    refine ⟨7269723547463100415989773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19385929459901601109306061 7269723547463100415989773)
                    ·
                      refine ⟨2726146330298662655996165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7269723547463100415989773 2726146330298662655996165)
                      ·
                        rfl

theorem cell23_5309151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_5309151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309151 prefixEnd_5309151 := by exact prefixLift 5309151
  have htrace : WordTrace (prefixWord ++ tailWord_5309151) baseStart_5309151 baseEnd_5309151 := by
    simpa [prefixWord, tailWord_5309151, baseEnd_5309151] using wordTrace_append hprefix tailTrace_5309151
  have hstable : (prefixWord ++ tailWord_5309151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309151).length < 2 ^ (prefixWord ++ tailWord_5309151).sum := by decide
  have hdescent : baseEnd_5309151 < baseStart_5309151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309161 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 3, 3, 2]
def baseStart_5309161 : Nat := 118140960795 + 5309161 * 2 ^ 59
def prefixEnd_5309161 : Nat := 4983230072969 + 3 ^ 40 * 5309161 * 2
def baseEnd_5309161 : Nat := 2726151465105207616871119

theorem tailTrace_5309161 : CollatzResearch.WordTrace tailWord_5309161 prefixEnd_5309161 2726151465105207616871119 := by
  unfold tailWord_5309161
  simp only [CollatzResearch.WordTrace]
  refine ⟨193641009918823904355247337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129094006612549269570164891 193641009918823904355247337)
  ·
    refine ⟨145230757439117928266435503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193641009918823904355247337 145230757439117928266435503)
    ·
      refine ⟨217846136158676892399653255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145230757439117928266435503 217846136158676892399653255)
      ·
        refine ⟨326769204238015338599479883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217846136158676892399653255 326769204238015338599479883)
        ·
          refine ⟨490153806357023007899219825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326769204238015338599479883 490153806357023007899219825)
          ·
            refine ⟨367615354767767255924414869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490153806357023007899219825 367615354767767255924414869)
            ·
              refine ⟨17231969754739090121456947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 367615354767767255924414869 17231969754739090121456947)
              ·
                refine ⟨25847954632108635182185421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17231969754739090121456947 25847954632108635182185421)
                ·
                  refine ⟨9692982987040738193319533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25847954632108635182185421 9692982987040738193319533)
                  ·
                    refine ⟨3634868620140276822494825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9692982987040738193319533 3634868620140276822494825)
                    ·
                      refine ⟨2726151465105207616871119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3634868620140276822494825 2726151465105207616871119)
                      ·
                        rfl

theorem cell23_5309161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 3, 2].length) (baseStart_5309161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309161 prefixEnd_5309161 := by exact prefixLift 5309161
  have htrace : WordTrace (prefixWord ++ tailWord_5309161) baseStart_5309161 baseEnd_5309161 := by
    simpa [prefixWord, tailWord_5309161, baseEnd_5309161] using wordTrace_append hprefix tailTrace_5309161
  have hstable : (prefixWord ++ tailWord_5309161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309161).length < 2 ^ (prefixWord ++ tailWord_5309161).sum := by decide
  have hdescent : baseEnd_5309161 < baseStart_5309161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309172 : List Nat := [2, 6, 1, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_5309172 : Nat := 118140960795 + 5309172 * 2 ^ 59
def prefixEnd_5309172 : Nat := 4983230072969 + 3 ^ 40 * 5309172 * 2
def baseEnd_5309172 : Nat := 2726157113392407073833569

theorem tailTrace_5309172 : CollatzResearch.WordTrace tailWord_5309172 prefixEnd_5309172 2726157113392407073833569 := by
  unfold tailWord_5309172
  simp only [CollatzResearch.WordTrace]
  refine ⟨96820705560892026616948885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129094274081189368822598513 96820705560892026616948885)
  ·
    refine ⟨4538470573166813747669479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 96820705560892026616948885 4538470573166813747669479)
    ·
      refine ⟨6807705859750220621504219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4538470573166813747669479 6807705859750220621504219)
      ·
        refine ⟨10211558789625330932256329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6807705859750220621504219 10211558789625330932256329)
        ·
          refine ⟨7658669092218998199192247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10211558789625330932256329 7658669092218998199192247)
          ·
            refine ⟨11488003638328497298788371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7658669092218998199192247 11488003638328497298788371)
            ·
              refine ⟨17232005457492745948182557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11488003638328497298788371 17232005457492745948182557)
              ·
                refine ⟨6462002046559779730568459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17232005457492745948182557 6462002046559779730568459)
                ·
                  refine ⟨9693003069839669595852689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6462002046559779730568459 9693003069839669595852689)
                  ·
                    refine ⟨7269752302379752196889517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9693003069839669595852689 7269752302379752196889517)
                    ·
                      refine ⟨2726157113392407073833569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7269752302379752196889517 2726157113392407073833569)
                      ·
                        rfl

theorem cell23_5309172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_5309172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309172 prefixEnd_5309172 := by exact prefixLift 5309172
  have htrace : WordTrace (prefixWord ++ tailWord_5309172) baseStart_5309172 baseEnd_5309172 := by
    simpa [prefixWord, tailWord_5309172, baseEnd_5309172] using wordTrace_append hprefix tailTrace_5309172
  have hstable : (prefixWord ++ tailWord_5309172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309172).length < 2 ^ (prefixWord ++ tailWord_5309172).sum := by decide
  have hdescent : baseEnd_5309172 < baseStart_5309172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309202 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_5309202 : Nat := 118140960795 + 5309202 * 2 ^ 59
def prefixEnd_5309202 : Nat := 4983230072969 + 3 ^ 40 * 5309202 * 2
def baseEnd_5309202 : Nat := 2726172517812041956458431

theorem tailTrace_5309202 : CollatzResearch.WordTrace tailWord_5309202 prefixEnd_5309202 2726172517812041956458431 := by
  unfold tailWord_5309202
  simp only [CollatzResearch.WordTrace]
  refine ⟨48410626327918842089372465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129095003541116912238326573 48410626327918842089372465)
  ·
    refine ⟨36307969745939131567029349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48410626327918842089372465 36307969745939131567029349)
    ·
      refine ⟨6807744327363587168818003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36307969745939131567029349 6807744327363587168818003)
      ·
        refine ⟨10211616491045380753227005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6807744327363587168818003 10211616491045380753227005)
        ·
          refine ⟨3829356184142017782460127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10211616491045380753227005 3829356184142017782460127)
          ·
            refine ⟨5744034276213026673690191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3829356184142017782460127 5744034276213026673690191)
            ·
              refine ⟨8616051414319540010535287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5744034276213026673690191 8616051414319540010535287)
              ·
                refine ⟨12924077121479310015802931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8616051414319540010535287 12924077121479310015802931)
                ·
                  refine ⟨19386115682218965023704397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12924077121479310015802931 19386115682218965023704397)
                  ·
                    refine ⟨7269793380832111883889149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19386115682218965023704397 7269793380832111883889149)
                    ·
                      refine ⟨2726172517812041956458431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7269793380832111883889149 2726172517812041956458431)
                      ·
                        rfl

theorem cell23_5309202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_5309202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309202 prefixEnd_5309202 := by exact prefixLift 5309202
  have htrace : WordTrace (prefixWord ++ tailWord_5309202) baseStart_5309202 baseEnd_5309202 := by
    simpa [prefixWord, tailWord_5309202, baseEnd_5309202] using wordTrace_append hprefix tailTrace_5309202
  have hstable : (prefixWord ++ tailWord_5309202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309202).length < 2 ^ (prefixWord ++ tailWord_5309202).sum := by decide
  have hdescent : baseEnd_5309202 < baseStart_5309202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309251 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 2, 5, 2]
def baseStart_5309251 : Nat := 118140960795 + 5309251 * 2 ^ 59
def prefixEnd_5309251 : Nat := 4983230072969 + 3 ^ 40 * 5309251 * 2
def baseEnd_5309251 : Nat := 2726197678364112264745705

theorem tailTrace_5309251 : CollatzResearch.WordTrace tailWord_5309251 prefixEnd_5309251 2726197678364112264745705 := by
  unfold tailWord_5309251
  simp only [CollatzResearch.WordTrace]
  refine ⟨193644292488497849726023607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129096194992331899817349071 193644292488497849726023607)
  ·
    refine ⟨290466438732746774589035411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193644292488497849726023607 290466438732746774589035411)
    ·
      refine ⟨435699658099120161883553117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290466438732746774589035411 435699658099120161883553117)
      ·
        refine ⟨163387371787170060706332419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435699658099120161883553117 163387371787170060706332419)
        ·
          refine ⟨245081057680755091059498629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163387371787170060706332419 245081057680755091059498629)
          ·
            refine ⟨45952698315141579573655993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245081057680755091059498629 45952698315141579573655993)
            ·
              refine ⟨34464523736356184680241995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45952698315141579573655993 34464523736356184680241995)
              ·
                refine ⟨51696785604534277020362993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34464523736356184680241995 51696785604534277020362993)
                ·
                  refine ⟨38772589203400707765272245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51696785604534277020362993 38772589203400707765272245)
                  ·
                    refine ⟨3634930237818816352994273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38772589203400707765272245 3634930237818816352994273)
                    ·
                      refine ⟨2726197678364112264745705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3634930237818816352994273 2726197678364112264745705)
                      ·
                        rfl

theorem cell23_5309251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 5, 2].length) (baseStart_5309251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309251 prefixEnd_5309251 := by exact prefixLift 5309251
  have htrace : WordTrace (prefixWord ++ tailWord_5309251) baseStart_5309251 baseEnd_5309251 := by
    simpa [prefixWord, tailWord_5309251, baseEnd_5309251] using wordTrace_append hprefix tailTrace_5309251
  have hstable : (prefixWord ++ tailWord_5309251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309251).length < 2 ^ (prefixWord ++ tailWord_5309251).sum := by decide
  have hdescent : baseEnd_5309251 < baseStart_5309251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309264 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 4]
def baseStart_5309264 : Nat := 118140960795 + 5309264 * 2 ^ 59
def prefixEnd_5309264 : Nat := 4983230072969 + 3 ^ 40 * 5309264 * 2
def baseEnd_5309264 : Nat := 2726204353612620713883145

theorem tailTrace_5309264 : CollatzResearch.WordTrace tailWord_5309264 prefixEnd_5309264 2726204353612620713883145 := by
  unfold tailWord_5309264
  simp only [CollatzResearch.WordTrace]
  refine ⟨96822383318725376473123423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129096511091633835297497897 96822383318725376473123423)
  ·
    refine ⟨145233574978088064709685135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96822383318725376473123423 145233574978088064709685135)
    ·
      refine ⟨217850362467132097064527703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145233574978088064709685135 217850362467132097064527703)
      ·
        refine ⟨326775543700698145596791555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217850362467132097064527703 326775543700698145596791555)
        ·
          refine ⟨490163315551047218395187333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326775543700698145596791555 490163315551047218395187333)
          ·
            refine ⟨91905621665821353449097625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 490163315551047218395187333 91905621665821353449097625)
            ·
              refine ⟨68929216249366015086823219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91905621665821353449097625 68929216249366015086823219)
              ·
                refine ⟨103393824374049022630234829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68929216249366015086823219 103393824374049022630234829)
                ·
                  refine ⟨38772684140268383486338061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 103393824374049022630234829 38772684140268383486338061)
                  ·
                    refine ⟨14539756552600643807376773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38772684140268383486338061 14539756552600643807376773)
                    ·
                      refine ⟨2726204353612620713883145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14539756552600643807376773 2726204353612620713883145)
                      ·
                        rfl

theorem cell23_5309264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_5309264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309264 prefixEnd_5309264 := by exact prefixLift 5309264
  have htrace : WordTrace (prefixWord ++ tailWord_5309264) baseStart_5309264 baseEnd_5309264 := by
    simpa [prefixWord, tailWord_5309264, baseEnd_5309264] using wordTrace_append hprefix tailTrace_5309264
  have hstable : (prefixWord ++ tailWord_5309264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309264).length < 2 ^ (prefixWord ++ tailWord_5309264).sum := by decide
  have hdescent : baseEnd_5309264 < baseStart_5309264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309281 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 3, 6, 2]
def baseStart_5309281 : Nat := 118140960795 + 5309281 * 2 ^ 59
def prefixEnd_5309281 : Nat := 4983230072969 + 3 ^ 40 * 5309281 * 2
def baseEnd_5309281 : Nat := 2726213082783747147370567

theorem tailTrace_5309281 : CollatzResearch.WordTrace tailWord_5309281 prefixEnd_5309281 2726213082783747147370567 := by
  unfold tailWord_5309281
  simp only [CollatzResearch.WordTrace]
  refine ⟨193645386678389164849615697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129096924452259443233077131 193645386678389164849615697)
  ·
    refine ⟨145234040008791873637211773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193645386678389164849615697 145234040008791873637211773)
    ·
      refine ⟨54462765003296952613954415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145234040008791873637211773 54462765003296952613954415)
      ·
        refine ⟨81694147504945428920931623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54462765003296952613954415 81694147504945428920931623)
        ·
          refine ⟨122541221257418143381397435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81694147504945428920931623 122541221257418143381397435)
          ·
            refine ⟨183811831886127215072096153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122541221257418143381397435 183811831886127215072096153)
            ·
              refine ⟨137858873914595411304072115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183811831886127215072096153 137858873914595411304072115)
              ·
                refine ⟨206788310871893116956108173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137858873914595411304072115 206788310871893116956108173)
                ·
                  refine ⟨77545616576959918858540565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206788310871893116956108173 77545616576959918858540565)
                  ·
                    refine ⟨3634950777044996196494089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77545616576959918858540565 3634950777044996196494089)
                    ·
                      refine ⟨2726213082783747147370567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3634950777044996196494089 2726213082783747147370567)
                      ·
                        rfl

theorem cell23_5309281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_5309281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309281 prefixEnd_5309281 := by exact prefixLift 5309281
  have htrace : WordTrace (prefixWord ++ tailWord_5309281) baseStart_5309281 baseEnd_5309281 := by
    simpa [prefixWord, tailWord_5309281, baseEnd_5309281] using wordTrace_append hprefix tailTrace_5309281
  have hstable : (prefixWord ++ tailWord_5309281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309281).length < 2 ^ (prefixWord ++ tailWord_5309281).sum := by decide
  have hdescent : baseEnd_5309281 < baseStart_5309281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309321 : List Nat := [1, 2, 1, 1, 5, 2, 2, 3, 6]
def baseStart_5309321 : Nat := 118140960795 + 5309321 * 2 ^ 59
def prefixEnd_5309321 : Nat := 4983230072969 + 3 ^ 40 * 5309321 * 2
def baseEnd_5309321 : Nat := 302914846889991887874487

theorem tailTrace_5309321 : CollatzResearch.WordTrace tailWord_5309321 prefixEnd_5309321 302914846889991887874487 := by
  unfold tailWord_5309321
  simp only [CollatzResearch.WordTrace]
  refine ⟨193646845598244251681071817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129097897065496167787381211 193646845598244251681071817)
  ·
    refine ⟨145235134198683188760803863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193646845598244251681071817 145235134198683188760803863)
    ·
      refine ⟨217852701298024783141205795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145235134198683188760803863 217852701298024783141205795)
      ·
        refine ⟨326779051947037174711808693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217852701298024783141205795 326779051947037174711808693)
        ·
          refine ⟨30635536120034735129232065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 326779051947037174711808693 30635536120034735129232065)
          ·
            refine ⟨22976652090026051346924049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30635536120034735129232065 22976652090026051346924049)
            ·
              refine ⟨17232489067519538510193037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22976652090026051346924049 17232489067519538510193037)
              ·
                refine ⟨6462183400319826941322389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17232489067519538510193037 6462183400319826941322389)
                ·
                  refine ⟨302914846889991887874487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6462183400319826941322389 302914846889991887874487)
                  ·
                    rfl

theorem cell23_5309321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 3, 6].length) (baseStart_5309321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309321 prefixEnd_5309321 := by exact prefixLift 5309321
  have htrace : WordTrace (prefixWord ++ tailWord_5309321) baseStart_5309321 baseEnd_5309321 := by
    simpa [prefixWord, tailWord_5309321, baseEnd_5309321] using wordTrace_append hprefix tailTrace_5309321
  have hstable : (prefixWord ++ tailWord_5309321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309321).length < 2 ^ (prefixWord ++ tailWord_5309321).sum := by decide
  have hdescent : baseEnd_5309321 < baseStart_5309321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309348 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 5, 1, 3]
def baseStart_5309348 : Nat := 118140960795 + 5309348 * 2 ^ 59
def prefixEnd_5309348 : Nat := 4983230072969 + 3 ^ 40 * 5309348 * 2
def baseEnd_5309348 : Nat := 2726247485987598385232759

theorem tailTrace_5309348 : CollatzResearch.WordTrace tailWord_5309348 prefixEnd_5309348 2726247485987598385232759 := by
  unfold tailWord_5309348
  simp only [CollatzResearch.WordTrace]
  refine ⟨96823915184573217646152349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129098553579430956861536465 96823915184573217646152349)
  ·
    refine ⟨36308968194214956617307131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96823915184573217646152349 36308968194214956617307131)
    ·
      refine ⟨54463452291322434925960697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36308968194214956617307131 54463452291322434925960697)
      ·
        refine ⟨40847589218491826194470523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54463452291322434925960697 40847589218491826194470523)
        ·
          refine ⟨61271383827737739291705785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40847589218491826194470523 61271383827737739291705785)
          ·
            refine ⟨45953537870803304468779339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61271383827737739291705785 45953537870803304468779339)
            ·
              refine ⟨68930306806204956703169009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45953537870803304468779339 68930306806204956703169009)
              ·
                refine ⟨51697730104653717527376757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68930306806204956703169009 51697730104653717527376757)
                ·
                  refine ⟨4846662197311286018191571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51697730104653717527376757 4846662197311286018191571)
                  ·
                    refine ⟨7269993295966929027287357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4846662197311286018191571 7269993295966929027287357)
                    ·
                      refine ⟨2726247485987598385232759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7269993295966929027287357 2726247485987598385232759)
                      ·
                        rfl

theorem cell23_5309348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_5309348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309348 prefixEnd_5309348 := by exact prefixLift 5309348
  have htrace : WordTrace (prefixWord ++ tailWord_5309348) baseStart_5309348 baseEnd_5309348 := by
    simpa [prefixWord, tailWord_5309348, baseEnd_5309348] using wordTrace_append hprefix tailTrace_5309348
  have hstable : (prefixWord ++ tailWord_5309348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309348).length < 2 ^ (prefixWord ++ tailWord_5309348).sum := by decide
  have hdescent : baseEnd_5309348 < baseStart_5309348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309365 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_5309365 : Nat := 118140960795 + 5309365 * 2 ^ 59
def prefixEnd_5309365 : Nat := 4983230072969 + 3 ^ 40 * 5309365 * 2
def baseEnd_5309365 : Nat := 2726256215158724818720181

theorem tailTrace_5309365 : CollatzResearch.WordTrace tailWord_5309365 prefixEnd_5309365 2726256215158724818720181 := by
  unfold tailWord_5309365
  simp only [CollatzResearch.WordTrace]
  refine ⟨193648450410084847195673549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129098966940056564797115699 193648450410084847195673549)
  ·
    refine ⟨72618168903781817698377581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193648450410084847195673549 72618168903781817698377581)
    ·
      refine ⟨27231813338918181636891593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72618168903781817698377581 27231813338918181636891593)
      ·
        refine ⟨20423860004188636227668695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27231813338918181636891593 20423860004188636227668695)
        ·
          refine ⟨30635790006282954341503043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20423860004188636227668695 30635790006282954341503043)
          ·
            refine ⟨45953685009424431512254565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30635790006282954341503043 45953685009424431512254565)
            ·
              refine ⟨8616315939267080908547731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45953685009424431512254565 8616315939267080908547731)
              ·
                refine ⟨12924473908900621362821597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8616315939267080908547731 12924473908900621362821597)
                ·
                  refine ⟨4846677715837733011058099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12924473908900621362821597 4846677715837733011058099)
                  ·
                    refine ⟨7270016573756599516587149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4846677715837733011058099 7270016573756599516587149)
                    ·
                      refine ⟨2726256215158724818720181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7270016573756599516587149 2726256215158724818720181)
                      ·
                        rfl

theorem cell23_5309365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_5309365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309365 prefixEnd_5309365 := by exact prefixLift 5309365
  have htrace : WordTrace (prefixWord ++ tailWord_5309365) baseStart_5309365 baseEnd_5309365 := by
    simpa [prefixWord, tailWord_5309365, baseEnd_5309365] using wordTrace_append hprefix tailTrace_5309365
  have hstable : (prefixWord ++ tailWord_5309365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309365).length < 2 ^ (prefixWord ++ tailWord_5309365).sum := by decide
  have hdescent : baseEnd_5309365 < baseStart_5309365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309388 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 2, 6, 2]
def baseStart_5309388 : Nat := 118140960795 + 5309388 * 2 ^ 59
def prefixEnd_5309388 : Nat := 4983230072969 + 3 ^ 40 * 5309388 * 2
def baseEnd_5309388 : Nat := 2726268025213778228732575

theorem tailTrace_5309388 : CollatzResearch.WordTrace tailWord_5309388 prefixEnd_5309388 2726268025213778228732575 := by
  unfold tailWord_5309388
  simp only [CollatzResearch.WordTrace]
  refine ⟨96824644644500761061880409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129099526192667681415840545 96824644644500761061880409)
  ·
    refine ⟨72618483483375570796410307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96824644644500761061880409 72618483483375570796410307)
    ·
      refine ⟨108927725225063356194615461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72618483483375570796410307 108927725225063356194615461)
      ·
        refine ⟨20423948479699379286490399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108927725225063356194615461 20423948479699379286490399)
        ·
          refine ⟨30635922719549068929735599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20423948479699379286490399 30635922719549068929735599)
          ·
            refine ⟨45953884079323603394603399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30635922719549068929735599 45953884079323603394603399)
            ·
              refine ⟨68930826118985405091905099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45953884079323603394603399 68930826118985405091905099)
              ·
                refine ⟨103396239178478107637857649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68930826118985405091905099 103396239178478107637857649)
                ·
                  refine ⟨77547179383858580728393237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103396239178478107637857649 77547179383858580728393237)
                  ·
                    refine ⟨3635024033618370971643433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77547179383858580728393237 3635024033618370971643433)
                    ·
                      refine ⟨2726268025213778228732575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3635024033618370971643433 2726268025213778228732575)
                      ·
                        rfl

theorem cell23_5309388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_5309388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309388 prefixEnd_5309388 := by exact prefixLift 5309388
  have htrace : WordTrace (prefixWord ++ tailWord_5309388) baseStart_5309388 baseEnd_5309388 := by
    simpa [prefixWord, tailWord_5309388, baseEnd_5309388] using wordTrace_append hprefix tailTrace_5309388
  have hstable : (prefixWord ++ tailWord_5309388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309388).length < 2 ^ (prefixWord ++ tailWord_5309388).sum := by decide
  have hdescent : baseEnd_5309388 < baseStart_5309388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309405 : List Nat := [1, 4, 3, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_5309405 : Nat := 118140960795 + 5309405 * 2 ^ 59
def prefixEnd_5309405 : Nat := 4983230072969 + 3 ^ 40 * 5309405 * 2
def baseEnd_5309405 : Nat := 2726276754384904662219997

theorem tailTrace_5309405 : CollatzResearch.WordTrace tailWord_5309405 prefixEnd_5309405 2726276754384904662219997 := by
  unfold tailWord_5309405
  simp only [CollatzResearch.WordTrace]
  refine ⟨193649909329939934027129669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129099939553293289351419779 193649909329939934027129669)
  ·
    refine ⟨36309357999363737630086813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193649909329939934027129669 36309357999363737630086813)
    ·
      refine ⟨13616009249761401611282555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36309357999363737630086813 13616009249761401611282555)
      ·
        refine ⟨20424013874642102416923833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13616009249761401611282555 20424013874642102416923833)
        ·
          refine ⟨15318010405981576812692875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20424013874642102416923833 15318010405981576812692875)
          ·
            refine ⟨22977015608972365219039313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15318010405981576812692875 22977015608972365219039313)
            ·
              refine ⟨17232761706729273914279485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22977015608972365219039313 17232761706729273914279485)
              ·
                refine ⟨6462285640023477717854807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17232761706729273914279485 6462285640023477717854807)
                ·
                  refine ⟨9693428460035216576782211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6462285640023477717854807 9693428460035216576782211)
                  ·
                    refine ⟨14540142690052824865173317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9693428460035216576782211 14540142690052824865173317)
                    ·
                      refine ⟨2726276754384904662219997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14540142690052824865173317 2726276754384904662219997)
                      ·
                        rfl

theorem cell23_5309405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_5309405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309405 prefixEnd_5309405 := by exact prefixLift 5309405
  have htrace : WordTrace (prefixWord ++ tailWord_5309405) baseStart_5309405 baseEnd_5309405 := by
    simpa [prefixWord, tailWord_5309405, baseEnd_5309405] using wordTrace_append hprefix tailTrace_5309405
  have hstable : (prefixWord ++ tailWord_5309405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309405).length < 2 ^ (prefixWord ++ tailWord_5309405).sum := by decide
  have hdescent : baseEnd_5309405 < baseStart_5309405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309465 : List Nat := [1, 2, 1, 2, 1, 1, 4, 5, 1, 3, 2]
def baseStart_5309465 : Nat := 118140960795 + 5309465 * 2 ^ 59
def prefixEnd_5309465 : Nat := 4983230072969 + 3 ^ 40 * 5309465 * 2
def baseEnd_5309465 : Nat := 2726307563224174427469721

theorem tailTrace_5309465 : CollatzResearch.WordTrace tailWord_5309465 prefixEnd_5309465 2726307563224174427469721 := by
  unfold tailWord_5309465
  simp only [CollatzResearch.WordTrace]
  refine ⟨193652097709722564274313849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129101398473148376182875899 193652097709722564274313849)
  ·
    refine ⟨145239073282291923205735387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193652097709722564274313849 145239073282291923205735387)
    ·
      refine ⟨217858609923437884808603081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145239073282291923205735387 217858609923437884808603081)
      ·
        refine ⟨163393957442578413606452311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217858609923437884808603081 163393957442578413606452311)
        ·
          refine ⟨245090936163867620409678467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163393957442578413606452311 245090936163867620409678467)
          ·
            refine ⟨367636404245801430614517701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245090936163867620409678467 367636404245801430614517701)
            ·
              refine ⟨68931825796087768240222069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 367636404245801430614517701 68931825796087768240222069)
              ·
                refine ⟨6462358668383228272520819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68931825796087768240222069 6462358668383228272520819)
                ·
                  refine ⟨9693538002574842408781229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6462358668383228272520819 9693538002574842408781229)
                  ·
                    refine ⟨3635076750965565903292961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9693538002574842408781229 3635076750965565903292961)
                    ·
                      refine ⟨2726307563224174427469721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3635076750965565903292961 2726307563224174427469721)
                      ·
                        rfl

theorem cell23_5309465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 3, 2].length) (baseStart_5309465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309465 prefixEnd_5309465 := by exact prefixLift 5309465
  have htrace : WordTrace (prefixWord ++ tailWord_5309465) baseStart_5309465 baseEnd_5309465 := by
    simpa [prefixWord, tailWord_5309465, baseEnd_5309465] using wordTrace_append hprefix tailTrace_5309465
  have hstable : (prefixWord ++ tailWord_5309465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309465).length < 2 ^ (prefixWord ++ tailWord_5309465).sum := by decide
  have hdescent : baseEnd_5309465 < baseStart_5309465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309495 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 6, 2, 2]
def baseStart_5309495 : Nat := 118140960795 + 5309495 * 2 ^ 59
def prefixEnd_5309495 : Nat := 4983230072969 + 3 ^ 40 * 5309495 * 2
def baseEnd_5309495 : Nat := 2726322967643809310094583

theorem tailTrace_5309495 : CollatzResearch.WordTrace tailWord_5309495 prefixEnd_5309495 2726322967643809310094583 := by
  unfold tailWord_5309495
  simp only [CollatzResearch.WordTrace]
  refine ⟨193653191899613879397905939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129102127933075919598603959 193653191899613879397905939)
  ·
    refine ⟨290479787849420819096858909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193653191899613879397905939 290479787849420819096858909)
    ·
      refine ⟨108929920443532807161322091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290479787849420819096858909 108929920443532807161322091)
      ·
        refine ⟨163394880665299210741983137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108929920443532807161322091 163394880665299210741983137)
        ·
          refine ⟨122546160498974408056487353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163394880665299210741983137 122546160498974408056487353)
          ·
            refine ⟨91909620374230806042365515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122546160498974408056487353 91909620374230806042365515)
            ·
              refine ⟨137864430561346209063548273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91909620374230806042365515 137864430561346209063548273)
              ·
                refine ⟨103398322921009656797661205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137864430561346209063548273 103398322921009656797661205)
                ·
                  refine ⟨4846796386922327662390369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103398322921009656797661205 4846796386922327662390369)
                  ·
                    refine ⟨3635097290191745746792777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4846796386922327662390369 3635097290191745746792777)
                    ·
                      refine ⟨2726322967643809310094583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3635097290191745746792777 2726322967643809310094583)
                      ·
                        rfl

theorem cell23_5309495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 2, 2].length) (baseStart_5309495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309495 prefixEnd_5309495 := by exact prefixLift 5309495
  have htrace : WordTrace (prefixWord ++ tailWord_5309495) baseStart_5309495 baseEnd_5309495 := by
    simpa [prefixWord, tailWord_5309495, baseEnd_5309495] using wordTrace_append hprefix tailTrace_5309495
  have hstable : (prefixWord ++ tailWord_5309495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309495).length < 2 ^ (prefixWord ++ tailWord_5309495).sum := by decide
  have hdescent : baseEnd_5309495 < baseStart_5309495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309528 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 4, 3, 3]
def baseStart_5309528 : Nat := 118140960795 + 5309528 * 2 ^ 59
def prefixEnd_5309528 : Nat := 4983230072969 + 3 ^ 40 * 5309528 * 2
def baseEnd_5309528 : Nat := 2726339912505407680981931

theorem tailTrace_5309528 : CollatzResearch.WordTrace tailWord_5309528 prefixEnd_5309528 2726339912505407680981931 := by
  unfold tailWord_5309528
  simp only [CollatzResearch.WordTrace]
  refine ⟨96827197754247163016928619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129102930338996217355904825 96827197754247163016928619)
  ·
    refine ⟨145240796631370744525392929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96827197754247163016928619 145240796631370744525392929)
    ·
      refine ⟨108930597473528058394044697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145240796631370744525392929 108930597473528058394044697)
      ·
        refine ⟨81697948105146043795533523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108930597473528058394044697 81697948105146043795533523)
        ·
          refine ⟨122546922157719065693300285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81697948105146043795533523 122546922157719065693300285)
          ·
            refine ⟨45955095809144649634987607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122546922157719065693300285 45955095809144649634987607)
            ·
              refine ⟨68932643713716974452481411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45955095809144649634987607 68932643713716974452481411)
              ·
                refine ⟨103398965570575461678722117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68932643713716974452481411 103398965570575461678722117)
                ·
                  refine ⟨19387306044482899064760397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103398965570575461678722117 19387306044482899064760397)
                  ·
                    refine ⟨7270239766681087149285149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19387306044482899064760397 7270239766681087149285149)
                    ·
                      refine ⟨2726339912505407680981931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7270239766681087149285149 2726339912505407680981931)
                      ·
                        rfl

theorem cell23_5309528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_5309528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309528 prefixEnd_5309528 := by exact prefixLift 5309528
  have htrace : WordTrace (prefixWord ++ tailWord_5309528) baseStart_5309528 baseEnd_5309528 := by
    simpa [prefixWord, tailWord_5309528, baseEnd_5309528] using wordTrace_append hprefix tailTrace_5309528
  have hstable : (prefixWord ++ tailWord_5309528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309528).length < 2 ^ (prefixWord ++ tailWord_5309528).sum := by decide
  have hdescent : baseEnd_5309528 < baseStart_5309528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309546 : List Nat := [3, 1, 3, 2, 2, 2, 3, 1, 2, 2, 2]
def baseStart_5309546 : Nat := 118140960795 + 5309546 * 2 ^ 59
def prefixEnd_5309546 : Nat := 4983230072969 + 3 ^ 40 * 5309546 * 2
def baseEnd_5309546 : Nat := 2726349155157188610556849

theorem tailTrace_5309546 : CollatzResearch.WordTrace tailWord_5309546 prefixEnd_5309546 2726349155157188610556849 := by
  unfold tailWord_5309546
  simp only [CollatzResearch.WordTrace]
  refine ⟨48413763005607278777003123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129103368014952743405341661 48413763005607278777003123)
  ·
    refine ⟨72620644508410918165504685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48413763005607278777003123 72620644508410918165504685)
    ·
      refine ⟨27232741690654094312064257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72620644508410918165504685 27232741690654094312064257)
      ·
        refine ⟨20424556267990570734048193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27232741690654094312064257 20424556267990570734048193)
        ·
          refine ⟨15318417200992928050536145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20424556267990570734048193 15318417200992928050536145)
          ·
            refine ⟨11488812900744696037902109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15318417200992928050536145 11488812900744696037902109)
            ·
              refine ⟨4308304837779261014213291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11488812900744696037902109 4308304837779261014213291)
              ·
                refine ⟨6462457256668891521319937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4308304837779261014213291 6462457256668891521319937)
                ·
                  refine ⟨4846842942501668640989953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6462457256668891521319937 4846842942501668640989953)
                  ·
                    refine ⟨3635132206876251480742465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4846842942501668640989953 3635132206876251480742465)
                    ·
                      refine ⟨2726349155157188610556849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3635132206876251480742465 2726349155157188610556849)
                      ·
                        rfl

theorem cell23_5309546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_5309546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309546 prefixEnd_5309546 := by exact prefixLift 5309546
  have htrace : WordTrace (prefixWord ++ tailWord_5309546) baseStart_5309546 baseEnd_5309546 := by
    simpa [prefixWord, tailWord_5309546, baseEnd_5309546] using wordTrace_append hprefix tailTrace_5309546
  have hstable : (prefixWord ++ tailWord_5309546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309546).length < 2 ^ (prefixWord ++ tailWord_5309546).sum := by decide
  have hdescent : baseEnd_5309546 < baseStart_5309546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309568 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 4]
def baseStart_5309568 : Nat := 118140960795 + 5309568 * 2 ^ 59
def prefixEnd_5309568 : Nat := 4983230072969 + 3 ^ 40 * 5309568 * 2
def baseEnd_5309568 : Nat := 2726360451731587524481747

theorem tailTrace_5309568 : CollatzResearch.WordTrace tailWord_5309568 prefixEnd_5309568 2726360451731587524481747 := by
  unfold tailWord_5309568
  simp only [CollatzResearch.WordTrace]
  refine ⟨96827927214174706432656679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129103902952232941910208905 96827927214174706432656679)
  ·
    refine ⟨145241890821262059648985019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96827927214174706432656679 145241890821262059648985019)
    ·
      refine ⟨217862836231893089473477529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145241890821262059648985019 217862836231893089473477529)
      ·
        refine ⟨163397127173919817105108147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217862836231893089473477529 163397127173919817105108147)
        ·
          refine ⟨245095690760879725657662221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163397127173919817105108147 245095690760879725657662221)
          ·
            refine ⟨91910884035329897121623333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245095690760879725657662221 91910884035329897121623333)
            ·
              refine ⟨17233290756624355710304375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91910884035329897121623333 17233290756624355710304375)
              ·
                refine ⟨25849936134936533565456563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17233290756624355710304375 25849936134936533565456563)
                ·
                  refine ⟨38774904202404800348184845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25849936134936533565456563 38774904202404800348184845)
                  ·
                    refine ⟨14540589075901800130569317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38774904202404800348184845 14540589075901800130569317)
                    ·
                      refine ⟨2726360451731587524481747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14540589075901800130569317 2726360451731587524481747)
                      ·
                        rfl

theorem cell23_5309568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_5309568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309568 prefixEnd_5309568 := by exact prefixLift 5309568
  have htrace : WordTrace (prefixWord ++ tailWord_5309568) baseStart_5309568 baseEnd_5309568 := by
    simpa [prefixWord, tailWord_5309568, baseEnd_5309568] using wordTrace_append hprefix tailTrace_5309568
  have hstable : (prefixWord ++ tailWord_5309568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309568).length < 2 ^ (prefixWord ++ tailWord_5309568).sum := by decide
  have hdescent : baseEnd_5309568 < baseStart_5309568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309635 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 7, 1, 3]
def baseStart_5309635 : Nat := 118140960795 + 5309635 * 2 ^ 59
def prefixEnd_5309635 : Nat := 4983230072969 + 3 ^ 40 * 5309635 * 2
def baseEnd_5309635 : Nat := 2726394854935438762343939

theorem tailTrace_5309635 : CollatzResearch.WordTrace tailWord_5309635 prefixEnd_5309635 2726394854935438762343939 := by
  unfold tailWord_5309635
  simp only [CollatzResearch.WordTrace]
  refine ⟨193658298119106683308002359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129105532079404455538668239 193658298119106683308002359)
  ·
    refine ⟨290487447178660024962003539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193658298119106683308002359 290487447178660024962003539)
    ·
      refine ⟨435731170767990037443005309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290487447178660024962003539 435731170767990037443005309)
      ·
        refine ⟨163399189037996264041126991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435731170767990037443005309 163399189037996264041126991)
        ·
          refine ⟨245098783556994396061690487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163399189037996264041126991 245098783556994396061690487)
          ·
            refine ⟨367648175335491594092535731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245098783556994396061690487 367648175335491594092535731)
            ·
              refine ⟨551472263003237391138803597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367648175335491594092535731 551472263003237391138803597)
              ·
                refine ⟨206802098626214021677051349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 551472263003237391138803597 206802098626214021677051349)
                ·
                  refine ⟨4846924186551891133055891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 206802098626214021677051349 4846924186551891133055891)
                  ·
                    refine ⟨7270386279827836699583837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4846924186551891133055891 7270386279827836699583837)
                    ·
                      refine ⟨2726394854935438762343939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7270386279827836699583837 2726394854935438762343939)
                      ·
                        rfl

theorem cell23_5309635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_5309635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309635 prefixEnd_5309635 := by exact prefixLift 5309635
  have htrace : WordTrace (prefixWord ++ tailWord_5309635) baseStart_5309635 baseEnd_5309635 := by
    simpa [prefixWord, tailWord_5309635, baseEnd_5309635] using wordTrace_append hprefix tailTrace_5309635
  have hstable : (prefixWord ++ tailWord_5309635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309635).length < 2 ^ (prefixWord ++ tailWord_5309635).sum := by decide
  have hdescent : baseEnd_5309635 < baseStart_5309635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309669 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 3, 1, 3]
def baseStart_5309669 : Nat := 118140960795 + 5309669 * 2 ^ 59
def prefixEnd_5309669 : Nat := 4983230072969 + 3 ^ 40 * 5309669 * 2
def baseEnd_5309669 : Nat := 2726412313277691629318783

theorem tailTrace_5309669 : CollatzResearch.WordTrace tailWord_5309669 prefixEnd_5309669 2726412313277691629318783 := by
  unfold tailWord_5309669
  simp only [CollatzResearch.WordTrace]
  refine ⟨193659538200983507114740061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129106358800655671409826707 193659538200983507114740061)
  ·
    refine ⟨72622326825368815168027523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193659538200983507114740061 72622326825368815168027523)
    ·
      refine ⟨108933490238053222752041285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72622326825368815168027523 108933490238053222752041285)
      ·
        refine ⟨20425029419634979266007741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108933490238053222752041285 20425029419634979266007741)
        ·
          refine ⟨7659386032363117224752903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20425029419634979266007741 7659386032363117224752903)
          ·
            refine ⟨11489079048544675837129355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7659386032363117224752903 11489079048544675837129355)
            ·
              refine ⟨17233618572817013755694033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11489079048544675837129355 17233618572817013755694033)
              ·
                refine ⟨12925213929612760316770525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17233618572817013755694033 12925213929612760316770525)
                ·
                  refine ⟨4846955223604785118788947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12925213929612760316770525 4846955223604785118788947)
                  ·
                    refine ⟨7270432835407177678183421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4846955223604785118788947 7270432835407177678183421)
                    ·
                      refine ⟨2726412313277691629318783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7270432835407177678183421 2726412313277691629318783)
                      ·
                        rfl

theorem cell23_5309669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_5309669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309669 prefixEnd_5309669 := by exact prefixLift 5309669
  have htrace : WordTrace (prefixWord ++ tailWord_5309669) baseStart_5309669 baseEnd_5309669 := by
    simpa [prefixWord, tailWord_5309669, baseEnd_5309669] using wordTrace_append hprefix tailTrace_5309669
  have hstable : (prefixWord ++ tailWord_5309669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309669).length < 2 ^ (prefixWord ++ tailWord_5309669).sum := by decide
  have hdescent : baseEnd_5309669 < baseStart_5309669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309675 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 4]
def baseStart_5309675 : Nat := 118140960795 + 5309675 * 2 ^ 59
def prefixEnd_5309675 : Nat := 4983230072969 + 3 ^ 40 * 5309675 * 2
def baseEnd_5309675 : Nat := 2726415394161618605843755

theorem tailTrace_5309675 : CollatzResearch.WordTrace tailWord_5309675 prefixEnd_5309675 2726415394161618605843755 := by
  unfold tailWord_5309675
  simp only [CollatzResearch.WordTrace]
  refine ⟨193659757038961770139458479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129106504692641180092972319 193659757038961770139458479)
  ·
    refine ⟨290489635558442655209187719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193659757038961770139458479 290489635558442655209187719)
    ·
      refine ⟨435734453337663982813781579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290489635558442655209187719 435734453337663982813781579)
      ·
        refine ⟨653601680006495974220672369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435734453337663982813781579 653601680006495974220672369)
        ·
          refine ⟨490201260004871980665504277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 653601680006495974220672369 490201260004871980665504277)
          ·
            refine ⟨22978184062728374093695513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 490201260004871980665504277 22978184062728374093695513)
            ·
              refine ⟨17233638047046280570271635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22978184062728374093695513 17233638047046280570271635)
              ·
                refine ⟨25850457070569420855407453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17233638047046280570271635 25850457070569420855407453)
                ·
                  refine ⟨9693921401463532820777795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25850457070569420855407453 9693921401463532820777795)
                  ·
                    refine ⟨14540882102195299231166693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9693921401463532820777795 14540882102195299231166693)
                    ·
                      refine ⟨2726415394161618605843755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14540882102195299231166693 2726415394161618605843755)
                      ·
                        rfl

theorem cell23_5309675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 4].length) (baseStart_5309675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309675 prefixEnd_5309675 := by exact prefixLift 5309675
  have htrace : WordTrace (prefixWord ++ tailWord_5309675) baseStart_5309675 baseEnd_5309675 := by
    simpa [prefixWord, tailWord_5309675, baseEnd_5309675] using wordTrace_append hprefix tailTrace_5309675
  have hstable : (prefixWord ++ tailWord_5309675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309675).length < 2 ^ (prefixWord ++ tailWord_5309675).sum := by decide
  have hdescent : baseEnd_5309675 < baseStart_5309675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309688 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_5309688 : Nat := 118140960795 + 5309688 * 2 ^ 59
def prefixEnd_5309688 : Nat := 4983230072969 + 3 ^ 40 * 5309688 * 2
def baseEnd_5309688 : Nat := 2726422069410127054981195

theorem tailTrace_5309688 : CollatzResearch.WordTrace tailWord_5309688 prefixEnd_5309688 2726422069410127054981195 := by
  unfold tailWord_5309688
  simp only [CollatzResearch.WordTrace]
  refine ⟨96830115593957336679840859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129106820791943115573121145 96830115593957336679840859)
  ·
    refine ⟨145245173390936005019761289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96830115593957336679840859 145245173390936005019761289)
    ·
      refine ⟨108933880043202003764820967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145245173390936005019761289 108933880043202003764820967)
      ·
        refine ⟨163400820064803005647231451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108933880043202003764820967 163400820064803005647231451)
        ·
          refine ⟨245101230097204508470847177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163400820064803005647231451 245101230097204508470847177)
          ·
            refine ⟨183825922572903381353135383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245101230097204508470847177 183825922572903381353135383)
            ·
              refine ⟨275738883859355072029703075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183825922572903381353135383 275738883859355072029703075)
              ·
                refine ⟨413608325789032608044554613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275738883859355072029703075 413608325789032608044554613)
                ·
                  refine ⟨38775780542721807004176995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 413608325789032608044554613 38775780542721807004176995)
                  ·
                    refine ⟨58163670814082710506265493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38775780542721807004176995 58163670814082710506265493)
                    ·
                      refine ⟨2726422069410127054981195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58163670814082710506265493 2726422069410127054981195)
                      ·
                        rfl

theorem cell23_5309688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_5309688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309688 prefixEnd_5309688 := by exact prefixLift 5309688
  have htrace : WordTrace (prefixWord ++ tailWord_5309688) baseStart_5309688 baseEnd_5309688 := by
    simpa [prefixWord, tailWord_5309688, baseEnd_5309688] using wordTrace_append hprefix tailTrace_5309688
  have hstable : (prefixWord ++ tailWord_5309688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309688).length < 2 ^ (prefixWord ++ tailWord_5309688).sum := by decide
  have hdescent : baseEnd_5309688 < baseStart_5309688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309719 : List Nat := [1, 1, 3, 4, 1, 1, 5, 1, 2, 4]
def baseStart_5309719 : Nat := 118140960795 + 5309719 * 2 ^ 59
def prefixEnd_5309719 : Nat := 4983230072969 + 3 ^ 40 * 5309719 * 2
def baseEnd_5309719 : Nat := 908812662436805477897851

theorem tailTrace_5309719 : CollatzResearch.WordTrace tailWord_5309719 prefixEnd_5309719 908812662436805477897851 := by
  unfold tailWord_5309719
  simp only [CollatzResearch.WordTrace]
  refine ⟨193661361850802365654060211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129107574567201577102706807 193661361850802365654060211)
  ·
    refine ⟨290492042776203548481090317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193661361850802365654060211 290492042776203548481090317)
    ·
      refine ⟨108934516041076330680408869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290492042776203548481090317 108934516041076330680408869)
      ·
        refine ⟨20425221757701812002576663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108934516041076330680408869 20425221757701812002576663)
        ·
          refine ⟨30637832636552718003864995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20425221757701812002576663 30637832636552718003864995)
          ·
            refine ⟨45956748954829077005797493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30637832636552718003864995 45956748954829077005797493)
            ·
              refine ⟨4308445214515225969293515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45956748954829077005797493 4308445214515225969293515)
              ·
                refine ⟨6462667821772838953940273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4308445214515225969293515 6462667821772838953940273)
                ·
                  refine ⟨4847000866329629215455205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6462667821772838953940273 4847000866329629215455205)
                  ·
                    refine ⟨908812662436805477897851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4847000866329629215455205 908812662436805477897851)
                    ·
                      rfl

theorem cell23_5309719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 2, 4].length) (baseStart_5309719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309719 prefixEnd_5309719 := by exact prefixLift 5309719
  have htrace : WordTrace (prefixWord ++ tailWord_5309719) baseStart_5309719 baseEnd_5309719 := by
    simpa [prefixWord, tailWord_5309719, baseEnd_5309719] using wordTrace_append hprefix tailTrace_5309719
  have hstable : (prefixWord ++ tailWord_5309719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309719).length < 2 ^ (prefixWord ++ tailWord_5309719).sum := by decide
  have hdescent : baseEnd_5309719 < baseStart_5309719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309722 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4]
def baseStart_5309722 : Nat := 118140960795 + 5309722 * 2 ^ 59
def prefixEnd_5309722 : Nat := 4983230072969 + 3 ^ 40 * 5309722 * 2
def baseEnd_5309722 : Nat := 2726439527752379921956039

theorem tailTrace_5309722 : CollatzResearch.WordTrace tailWord_5309722 prefixEnd_5309722 2726439527752379921956039 := by
  unfold tailWord_5309722
  simp only [CollatzResearch.WordTrace]
  refine ⟨48415367817447874291604855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129107647513194331444279613 48415367817447874291604855)
  ·
    refine ⟨72623051726171811437407283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48415367817447874291604855 72623051726171811437407283)
    ·
      refine ⟨108934577589257717156110925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72623051726171811437407283 108934577589257717156110925)
      ·
        refine ⟨40850466595971643933541597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108934577589257717156110925 40850466595971643933541597)
        ·
          refine ⟨15318924973489366475078099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40850466595971643933541597 15318924973489366475078099)
          ·
            refine ⟨22978387460234049712617149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15318924973489366475078099 22978387460234049712617149)
            ·
              refine ⟨8616895297587768642231431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22978387460234049712617149 8616895297587768642231431)
              ·
                refine ⟨12925342946381652963347147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8616895297587768642231431 12925342946381652963347147)
                ·
                  refine ⟨19388014419572479445020721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12925342946381652963347147 19388014419572479445020721)
                  ·
                    refine ⟨14541010814679359583765541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19388014419572479445020721 14541010814679359583765541)
                    ·
                      refine ⟨2726439527752379921956039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14541010814679359583765541 2726439527752379921956039)
                      ·
                        rfl

theorem cell23_5309722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_5309722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309722 prefixEnd_5309722 := by exact prefixLift 5309722
  have htrace : WordTrace (prefixWord ++ tailWord_5309722) baseStart_5309722 baseEnd_5309722 := by
    simpa [prefixWord, tailWord_5309722, baseEnd_5309722] using wordTrace_append hprefix tailTrace_5309722
  have hstable : (prefixWord ++ tailWord_5309722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309722).length < 2 ^ (prefixWord ++ tailWord_5309722).sum := by decide
  have hdescent : baseEnd_5309722 < baseStart_5309722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
