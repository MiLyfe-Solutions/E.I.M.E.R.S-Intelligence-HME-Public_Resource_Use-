import V185TrunkScan20Chunk087

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_535757 : List Nat := [1, 6, 2, 2, 1, 2, 2, 4]
def baseStart_535757 : Nat := 118140960795 + 535757 * 2 ^ 59
def prefixEnd_535757 : Nat := 4983230072969 + 3 ^ 40 * 535757 * 2
def baseEnd_535757 : Nat := 81511364447693505769957

theorem tailTrace_535757 : CollatzResearch.WordTrace tailWord_535757 prefixEnd_535757 81511364447693505769957 := by
  unfold tailWord_535757
  simp only [CollatzResearch.WordTrace]
  refine ⟨19540663120051363856021525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13027108746700909237347683 19540663120051363856021525)
  ·
    refine ⟨915968583752407680751009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19540663120051363856021525 915968583752407680751009)
    ·
      refine ⟨686976437814305760563257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 915968583752407680751009 686976437814305760563257)
      ·
        refine ⟨515232328360729320422443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 686976437814305760563257 515232328360729320422443)
        ·
          refine ⟨772848492541093980633665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515232328360729320422443 772848492541093980633665)
          ·
            refine ⟨579636369405820485475249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 772848492541093980633665 579636369405820485475249)
            ·
              refine ⟨434727277054365364106437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579636369405820485475249 434727277054365364106437)
              ·
                refine ⟨81511364447693505769957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 434727277054365364106437 81511364447693505769957)
                ·
                  rfl

theorem cell20_535757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 4].length) (baseStart_535757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535757 prefixEnd_535757 := by exact prefixLift 535757
  have htrace : WordTrace (prefixWord ++ tailWord_535757) baseStart_535757 baseEnd_535757 := by
    simpa [prefixWord, tailWord_535757, baseEnd_535757] using wordTrace_append hprefix tailTrace_535757
  have hstable : (prefixWord ++ tailWord_535757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535757).length < 2 ^ (prefixWord ++ tailWord_535757).sum := by decide
  have hdescent : baseEnd_535757 < baseStart_535757 := by decide
  rcases family_descends (prefixWord ++ tailWord_535757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535775 : List Nat := [1, 1, 2, 3, 2, 1, 5, 3, 2]
def baseStart_535775 : Nat := 118140960795 + 535775 * 2 ^ 59
def prefixEnd_535775 : Nat := 4983230072969 + 3 ^ 40 * 535775 * 2
def baseEnd_535775 : Nat := 244542309033552454709797

theorem tailTrace_535775 : CollatzResearch.WordTrace tailWord_535775 prefixEnd_535775 244542309033552454709797 := by
  unfold tailWord_535775
  simp only [CollatzResearch.WordTrace]
  refine ⟨19541319633986152930176779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13027546422657435286784519 19541319633986152930176779)
  ·
    refine ⟨29311979450979229395265169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19541319633986152930176779 29311979450979229395265169)
    ·
      refine ⟨21983984588234422046448877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29311979450979229395265169 21983984588234422046448877)
      ·
        refine ⟨8243994220587908267418329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21983984588234422046448877 8243994220587908267418329)
        ·
          refine ⟨6182995665440931200563747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8243994220587908267418329 6182995665440931200563747)
          ·
            refine ⟨9274493498161396800845621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6182995665440931200563747 9274493498161396800845621)
            ·
              refine ⟨869483765452630950079277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9274493498161396800845621 869483765452630950079277)
              ·
                refine ⟨326056412044736606279729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 869483765452630950079277 326056412044736606279729)
                ·
                  refine ⟨244542309033552454709797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326056412044736606279729 244542309033552454709797)
                  ·
                    rfl

theorem cell20_535775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 3, 2].length) (baseStart_535775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535775 prefixEnd_535775 := by exact prefixLift 535775
  have htrace : WordTrace (prefixWord ++ tailWord_535775) baseStart_535775 baseEnd_535775 := by
    simpa [prefixWord, tailWord_535775, baseEnd_535775] using wordTrace_append hprefix tailTrace_535775
  have hstable : (prefixWord ++ tailWord_535775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535775).length < 2 ^ (prefixWord ++ tailWord_535775).sum := by decide
  have hdescent : baseEnd_535775 < baseStart_535775 := by decide
  rcases family_descends (prefixWord ++ tailWord_535775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535789 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 5]
def baseStart_535789 : Nat := 118140960795 + 535789 * 2 ^ 59
def prefixEnd_535789 : Nat := 4983230072969 + 3 ^ 40 * 535789 * 2
def baseEnd_535789 : Nat := 244548699015030628243073

theorem tailTrace_535789 : CollatzResearch.WordTrace tailWord_535789 prefixEnd_535789 244548699015030628243073 := by
  unfold tailWord_535789
  simp only [CollatzResearch.WordTrace]
  refine ⟨19541830255935433321186421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13027886837290288880790947 19541830255935433321186421)
  ·
    refine ⟨1832046586493946873861227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19541830255935433321186421 1832046586493946873861227)
    ·
      refine ⟨2748069879740920310791841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1832046586493946873861227 2748069879740920310791841)
      ·
        refine ⟨2061052409805690233093881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2748069879740920310791841 2061052409805690233093881)
        ·
          refine ⟨1545789307354267674820411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2061052409805690233093881 1545789307354267674820411)
          ·
            refine ⟨2318683961031401512230617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1545789307354267674820411 2318683961031401512230617)
            ·
              refine ⟨1739012970773551134172963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2318683961031401512230617 1739012970773551134172963)
              ·
                refine ⟨2608519456160326701259445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1739012970773551134172963 2608519456160326701259445)
                ·
                  refine ⟨244548699015030628243073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2608519456160326701259445 244548699015030628243073)
                  ·
                    rfl

theorem cell20_535789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_535789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535789 prefixEnd_535789 := by exact prefixLift 535789
  have htrace : WordTrace (prefixWord ++ tailWord_535789) baseStart_535789 baseEnd_535789 := by
    simpa [prefixWord, tailWord_535789, baseEnd_535789] using wordTrace_append hprefix tailTrace_535789
  have hstable : (prefixWord ++ tailWord_535789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535789).length < 2 ^ (prefixWord ++ tailWord_535789).sum := by decide
  have hdescent : baseEnd_535789 < baseStart_535789 := by decide
  rcases family_descends (prefixWord ++ tailWord_535789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535806 : List Nat := [4, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_535806 : Nat := 118140960795 + 535806 * 2 ^ 59
def prefixEnd_535806 : Nat := 4983230072969 + 3 ^ 40 * 535806 * 2
def baseEnd_535806 : Nat := 244556458278254124676337

theorem tailTrace_535806 : CollatzResearch.WordTrace tailWord_535806 prefixEnd_535806 244556458278254124676337 := by
  unfold tailWord_535806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2442806287109230653069409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13028300197915896816370181 2442806287109230653069409)
  ·
    refine ⟨1832104715331922989802057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2442806287109230653069409 1832104715331922989802057)
    ·
      refine ⟨1374078536498942242351543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1832104715331922989802057 1374078536498942242351543)
      ·
        refine ⟨2061117804748413363527315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1374078536498942242351543 2061117804748413363527315)
        ·
          refine ⟨3091676707122620045290973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2061117804748413363527315 3091676707122620045290973)
          ·
            refine ⟨1159378765170982516984115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3091676707122620045290973 1159378765170982516984115)
            ·
              refine ⟨1739068147756473775476173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159378765170982516984115 1739068147756473775476173)
              ·
                refine ⟨652150555408677665803565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1739068147756473775476173 652150555408677665803565)
                ·
                  refine ⟨244556458278254124676337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 652150555408677665803565 244556458278254124676337)
                  ·
                    rfl

theorem cell20_535806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_535806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535806 prefixEnd_535806 := by exact prefixLift 535806
  have htrace : WordTrace (prefixWord ++ tailWord_535806) baseStart_535806 baseEnd_535806 := by
    simpa [prefixWord, tailWord_535806, baseEnd_535806] using wordTrace_append hprefix tailTrace_535806
  have hstable : (prefixWord ++ tailWord_535806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535806).length < 2 ^ (prefixWord ++ tailWord_535806).sum := by decide
  have hdescent : baseEnd_535806 < baseStart_535806 := by decide
  rcases family_descends (prefixWord ++ tailWord_535806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535817 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 6]
def baseStart_535817 : Nat := 118140960795 + 535817 * 2 ^ 59
def prefixEnd_535817 : Nat := 4983230072969 + 3 ^ 40 * 535817 * 2
def baseEnd_535817 : Nat := 244561478977986975309625

theorem tailTrace_535817 : CollatzResearch.WordTrace tailWord_535817 prefixEnd_535817 244561478977986975309625 := by
  unfold tailWord_535817
  simp only [CollatzResearch.WordTrace]
  refine ⟨19542851499833994103205705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13028567666555996068803803 19542851499833994103205705)
  ·
    refine ⟨14657138624875495577404279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19542851499833994103205705 14657138624875495577404279)
    ·
      refine ⟨21985707937313243366106419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14657138624875495577404279 21985707937313243366106419)
      ·
        refine ⟨32978561905969865049159629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21985707937313243366106419 32978561905969865049159629)
        ·
          refine ⟨12366960714738699393434861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32978561905969865049159629 12366960714738699393434861)
          ·
            refine ⟨4637610268027012272538073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12366960714738699393434861 4637610268027012272538073)
            ·
              refine ⟨3478207701020259204403555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4637610268027012272538073 3478207701020259204403555)
              ·
                refine ⟨5217311551530388806605333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3478207701020259204403555 5217311551530388806605333)
                ·
                  refine ⟨244561478977986975309625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5217311551530388806605333 244561478977986975309625)
                  ·
                    rfl

theorem cell20_535817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_535817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535817 prefixEnd_535817 := by exact prefixLift 535817
  have htrace : WordTrace (prefixWord ++ tailWord_535817) baseStart_535817 baseEnd_535817 := by
    simpa [prefixWord, tailWord_535817, baseEnd_535817] using wordTrace_append hprefix tailTrace_535817
  have hstable : (prefixWord ++ tailWord_535817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535817).length < 2 ^ (prefixWord ++ tailWord_535817).sum := by decide
  have hdescent : baseEnd_535817 < baseStart_535817 := by decide
  rcases family_descends (prefixWord ++ tailWord_535817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535855 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 4]
def baseStart_535855 : Nat := 118140960795 + 535855 * 2 ^ 59
def prefixEnd_535855 : Nat := 4983230072969 + 3 ^ 40 * 535855 * 2
def baseEnd_535855 : Nat := 244578823213427732042803

theorem tailTrace_535855 : CollatzResearch.WordTrace tailWord_535855 prefixEnd_535855 244578823213427732042803 := by
  unfold tailWord_535855
  simp only [CollatzResearch.WordTrace]
  refine ⟨19544237473696326593089019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13029491649130884395392679 19544237473696326593089019)
  ·
    refine ⟨29316356210544489889633529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19544237473696326593089019 29316356210544489889633529)
    ·
      refine ⟨21987267157908367417225147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29316356210544489889633529 21987267157908367417225147)
      ·
        refine ⟨32980900736862551125837721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21987267157908367417225147 32980900736862551125837721)
        ·
          refine ⟨24735675552646913344378291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32980900736862551125837721 24735675552646913344378291)
          ·
            refine ⟨37103513328970370016567437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24735675552646913344378291 37103513328970370016567437)
            ·
              refine ⟨13913817498363888756212789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37103513328970370016567437 13913817498363888756212789)
              ·
                refine ⟨1304420390471614570894949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13913817498363888756212789 1304420390471614570894949)
                ·
                  refine ⟨244578823213427732042803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1304420390471614570894949 244578823213427732042803)
                  ·
                    rfl

theorem cell20_535855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_535855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535855 prefixEnd_535855 := by exact prefixLift 535855
  have htrace : WordTrace (prefixWord ++ tailWord_535855) baseStart_535855 baseEnd_535855 := by
    simpa [prefixWord, tailWord_535855, baseEnd_535855] using wordTrace_append hprefix tailTrace_535855
  have hstable : (prefixWord ++ tailWord_535855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535855).length < 2 ^ (prefixWord ++ tailWord_535855).sum := by decide
  have hdescent : baseEnd_535855 < baseStart_535855 := by decide
  rcases family_descends (prefixWord ++ tailWord_535855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535858 : List Nat := [3, 2, 1, 1, 4, 3, 1, 5]
def baseStart_535858 : Nat := 118140960795 + 535858 * 2 ^ 59
def prefixEnd_535858 : Nat := 4983230072969 + 3 ^ 40 * 535858 * 2
def baseEnd_535858 : Nat := 81526730831724351647597

theorem tailTrace_535858 : CollatzResearch.WordTrace tailWord_535858 prefixEnd_535858 81526730831724351647597 := by
  unfold tailWord_535858
  simp only [CollatzResearch.WordTrace]
  refine ⟨4886086723171364526362057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13029564595123638736965485 4886086723171364526362057)
  ·
    refine ⟨3664565042378523394771543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4886086723171364526362057 3664565042378523394771543)
    ·
      refine ⟨5496847563567785092157315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3664565042378523394771543 5496847563567785092157315)
      ·
        refine ⟨8245271345351677638235973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5496847563567785092157315 8245271345351677638235973)
        ·
          refine ⟨1545988377253439557169245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8245271345351677638235973 1545988377253439557169245)
          ·
            refine ⟨579745641470039833938467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1545988377253439557169245 579745641470039833938467)
            ·
              refine ⟨869618462205059750907701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579745641470039833938467 869618462205059750907701)
              ·
                refine ⟨81526730831724351647597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 869618462205059750907701 81526730831724351647597)
                ·
                  rfl

theorem cell20_535858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_535858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535858 prefixEnd_535858 := by exact prefixLift 535858
  have htrace : WordTrace (prefixWord ++ tailWord_535858) baseStart_535858 baseEnd_535858 := by
    simpa [prefixWord, tailWord_535858, baseEnd_535858] using wordTrace_append hprefix tailTrace_535858
  have hstable : (prefixWord ++ tailWord_535858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535858).length < 2 ^ (prefixWord ++ tailWord_535858).sum := by decide
  have hdescent : baseEnd_535858 < baseStart_535858 := by decide
  rcases family_descends (prefixWord ++ tailWord_535858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535886 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_535886 : Nat := 118140960795 + 535886 * 2 ^ 59
def prefixEnd_535886 : Nat := 4983230072969 + 3 ^ 40 * 535886 * 2
def baseEnd_535886 : Nat := 244592972458129402009343

theorem tailTrace_535886 : CollatzResearch.WordTrace tailWord_535886 prefixEnd_535886 244592972458129402009343 := by
  unfold tailWord_535886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2443171017073002360933439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13030245424389345924978341 2443171017073002360933439)
  ·
    refine ⟨3664756525609503541400159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2443171017073002360933439 3664756525609503541400159)
    ·
      refine ⟨5497134788414255312100239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3664756525609503541400159 5497134788414255312100239)
      ·
        refine ⟨8245702182621382968150359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5497134788414255312100239 8245702182621382968150359)
        ·
          refine ⟨12368553273932074452225539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8245702182621382968150359 12368553273932074452225539)
          ·
            refine ⟨18552829910898111678338309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12368553273932074452225539 18552829910898111678338309)
            ·
              refine ⟨3478655608293395939688433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18552829910898111678338309 3478655608293395939688433)
              ·
                refine ⟨2608991706220046954766325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3478655608293395939688433 2608991706220046954766325)
                ·
                  refine ⟨244592972458129402009343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2608991706220046954766325 244592972458129402009343)
                  ·
                    rfl

theorem cell20_535886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_535886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535886 prefixEnd_535886 := by exact prefixLift 535886
  have htrace : WordTrace (prefixWord ++ tailWord_535886) baseStart_535886 baseEnd_535886 := by
    simpa [prefixWord, tailWord_535886, baseEnd_535886] using wordTrace_append hprefix tailTrace_535886
  have hstable : (prefixWord ++ tailWord_535886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535886).length < 2 ^ (prefixWord ++ tailWord_535886).sum := by decide
  have hdescent : baseEnd_535886 < baseStart_535886 := by decide
  rcases family_descends (prefixWord ++ tailWord_535886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535889 : List Nat := [1, 2, 2, 1, 4, 1, 4, 3, 2]
def baseStart_535889 : Nat := 118140960795 + 535889 * 2 ^ 59
def prefixEnd_535889 : Nat := 4983230072969 + 3 ^ 40 * 535889 * 2
def baseEnd_535889 : Nat := 244594341739874724909331

theorem tailTrace_535889 : CollatzResearch.WordTrace tailWord_535889 prefixEnd_535889 244594341739874724909331 := by
  unfold tailWord_535889
  simp only [CollatzResearch.WordTrace]
  refine ⟨19545477555573150399826721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13030318370382100266551147 19545477555573150399826721)
  ·
    refine ⟨14659108166679862799870041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19545477555573150399826721 14659108166679862799870041)
    ·
      refine ⟨10994331125009897099902531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14659108166679862799870041 10994331125009897099902531)
      ·
        refine ⟨16491496687514845649853797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10994331125009897099902531 16491496687514845649853797)
        ·
          refine ⟨3092155628909033559347587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16491496687514845649853797 3092155628909033559347587)
          ·
            refine ⟨4638233443363550339021381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3092155628909033559347587 4638233443363550339021381)
            ·
              refine ⟨869668770630665688566509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4638233443363550339021381 869668770630665688566509)
              ·
                refine ⟨326125788986499633212441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 869668770630665688566509 326125788986499633212441)
                ·
                  refine ⟨244594341739874724909331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326125788986499633212441 244594341739874724909331)
                  ·
                    rfl

theorem cell20_535889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 2].length) (baseStart_535889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535889 prefixEnd_535889 := by exact prefixLift 535889
  have htrace : WordTrace (prefixWord ++ tailWord_535889) baseStart_535889 baseEnd_535889 := by
    simpa [prefixWord, tailWord_535889, baseEnd_535889] using wordTrace_append hprefix tailTrace_535889
  have hstable : (prefixWord ++ tailWord_535889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535889).length < 2 ^ (prefixWord ++ tailWord_535889).sum := by decide
  have hdescent : baseEnd_535889 < baseStart_535889 := by decide
  rcases family_descends (prefixWord ++ tailWord_535889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535931 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 4]
def baseStart_535931 : Nat := 118140960795 + 535931 * 2 ^ 59
def prefixEnd_535931 : Nat := 4983230072969 + 3 ^ 40 * 535931 * 2
def baseEnd_535931 : Nat := 244613511684309245509159

theorem tailTrace_535931 : CollatzResearch.WordTrace tailWord_535931 prefixEnd_535931 244613511684309245509159 := by
  unfold tailWord_535931
  simp only [CollatzResearch.WordTrace]
  refine ⟨19547009421420991572855647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13031339614280661048570431 19547009421420991572855647)
  ·
    refine ⟨29320514132131487359283471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19547009421420991572855647 29320514132131487359283471)
    ·
      refine ⟨43980771198197231038925207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29320514132131487359283471 43980771198197231038925207)
      ·
        refine ⟨65971156797295846558387811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43980771198197231038925207 65971156797295846558387811)
        ·
          refine ⟨98956735195943769837581717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65971156797295846558387811 98956735195943769837581717)
          ·
            refine ⟨4638596962309864211136643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 98956735195943769837581717 4638596962309864211136643)
            ·
              refine ⟨6957895443464796316704965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4638596962309864211136643 6957895443464796316704965)
              ·
                refine ⟨1304605395649649309382181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6957895443464796316704965 1304605395649649309382181)
                ·
                  refine ⟨244613511684309245509159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1304605395649649309382181 244613511684309245509159)
                  ·
                    rfl

theorem cell20_535931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_535931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535931 prefixEnd_535931 := by exact prefixLift 535931
  have htrace : WordTrace (prefixWord ++ tailWord_535931) baseStart_535931 baseEnd_535931 := by
    simpa [prefixWord, tailWord_535931, baseEnd_535931] using wordTrace_append hprefix tailTrace_535931
  have hstable : (prefixWord ++ tailWord_535931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535931).length < 2 ^ (prefixWord ++ tailWord_535931).sum := by decide
  have hdescent : baseEnd_535931 < baseStart_535931 := by decide
  rcases family_descends (prefixWord ++ tailWord_535931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535944 : List Nat := [2, 1, 3, 3, 1, 4, 1, 3, 2]
def baseStart_535944 : Nat := 118140960795 + 535944 * 2 ^ 59
def prefixEnd_535944 : Nat := 4983230072969 + 3 ^ 40 * 535944 * 2
def baseEnd_535944 : Nat := 244619445238538978075773

theorem tailTrace_535944 : CollatzResearch.WordTrace tailWord_535944 prefixEnd_535944 244619445238538978075773 := by
  unfold tailWord_535944
  simp only [CollatzResearch.WordTrace]
  refine ⟨9773741785186947396539443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13031655713582596528719257 9773741785186947396539443)
  ·
    refine ⟨14660612677780421094809165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9773741785186947396539443 14660612677780421094809165)
    ·
      refine ⟨5497729754167657910553437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14660612677780421094809165 5497729754167657910553437)
      ·
        refine ⟨2061648657812871716457539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5497729754167657910553437 2061648657812871716457539)
        ·
          refine ⟨3092472986719307574686309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2061648657812871716457539 3092472986719307574686309)
          ·
            refine ⟨579838685009870170253683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3092472986719307574686309 579838685009870170253683)
            ·
              refine ⟨869758027514805255380525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579838685009870170253683 869758027514805255380525)
              ·
                refine ⟨326159260318051970767697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 869758027514805255380525 326159260318051970767697)
                ·
                  refine ⟨244619445238538978075773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326159260318051970767697 244619445238538978075773)
                  ·
                    rfl

theorem cell20_535944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 3, 2].length) (baseStart_535944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535944 prefixEnd_535944 := by exact prefixLift 535944
  have htrace : WordTrace (prefixWord ++ tailWord_535944) baseStart_535944 baseEnd_535944 := by
    simpa [prefixWord, tailWord_535944, baseEnd_535944] using wordTrace_append hprefix tailTrace_535944
  have hstable : (prefixWord ++ tailWord_535944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535944).length < 2 ^ (prefixWord ++ tailWord_535944).sum := by decide
  have hdescent : baseEnd_535944 < baseStart_535944 := by decide
  rcases family_descends (prefixWord ++ tailWord_535944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535962 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_535962 : Nat := 118140960795 + 535962 * 2 ^ 59
def prefixEnd_535962 : Nat := 4983230072969 + 3 ^ 40 * 535962 * 2
def baseEnd_535962 : Nat := 244627660929010915475699

theorem tailTrace_535962 : CollatzResearch.WordTrace tailWord_535962 prefixEnd_535962 244627660929010915475699 := by
  unfold tailWord_535962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4887035021077170966808535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13032093389539122578156093 4887035021077170966808535)
  ·
    refine ⟨7330552531615756450212803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4887035021077170966808535 7330552531615756450212803)
    ·
      refine ⟨10995828797423634675319205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7330552531615756450212803 10995828797423634675319205)
      ·
        refine ⟨2061717899516931501622351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10995828797423634675319205 2061717899516931501622351)
        ·
          refine ⟨3092576849275397252433527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2061717899516931501622351 3092576849275397252433527)
          ·
            refine ⟨4638865273913095878650291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3092576849275397252433527 4638865273913095878650291)
            ·
              refine ⟨6958297910869643817975437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4638865273913095878650291 6958297910869643817975437)
              ·
                refine ⟨2609361716576116431740789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6958297910869643817975437 2609361716576116431740789)
                ·
                  refine ⟨244627660929010915475699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2609361716576116431740789 244627660929010915475699)
                  ·
                    rfl

theorem cell20_535962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_535962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535962 prefixEnd_535962 := by exact prefixLift 535962
  have htrace : WordTrace (prefixWord ++ tailWord_535962) baseStart_535962 baseEnd_535962 := by
    simpa [prefixWord, tailWord_535962, baseEnd_535962] using wordTrace_append hprefix tailTrace_535962
  have hstable : (prefixWord ++ tailWord_535962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535962).length < 2 ^ (prefixWord ++ tailWord_535962).sum := by decide
  have hdescent : baseEnd_535962 < baseStart_535962 := by decide
  rcases family_descends (prefixWord ++ tailWord_535962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_535965 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 4]
def baseStart_535965 : Nat := 118140960795 + 535965 * 2 ^ 59
def prefixEnd_535965 : Nat := 4983230072969 + 3 ^ 40 * 535965 * 2
def baseEnd_535965 : Nat := 244629030210756238375687

theorem tailTrace_535965 : CollatzResearch.WordTrace tailWord_535965 prefixEnd_535965 244629030210756238375687 := by
  unfold tailWord_535965
  simp only [CollatzResearch.WordTrace]
  refine ⟨19548249503297815379593349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13032166335531876919728899 19548249503297815379593349)
  ·
    refine ⟨3665296781868340383673753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19548249503297815379593349 3665296781868340383673753)
    ·
      refine ⟨2748972586401255287755315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3665296781868340383673753 2748972586401255287755315)
      ·
        refine ⟨4123458879601882931632973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2748972586401255287755315 4123458879601882931632973)
        ·
          refine ⟨1546297079850706099362365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4123458879601882931632973 1546297079850706099362365)
          ·
            refine ⟨579861404944014787260887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1546297079850706099362365 579861404944014787260887)
            ·
              refine ⟨869792107416022180891331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579861404944014787260887 869792107416022180891331)
              ·
                refine ⟨1304688161124033271336997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 869792107416022180891331 1304688161124033271336997)
                ·
                  refine ⟨244629030210756238375687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1304688161124033271336997 244629030210756238375687)
                  ·
                    rfl

theorem cell20_535965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_535965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_535965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_535965 prefixEnd_535965 := by exact prefixLift 535965
  have htrace : WordTrace (prefixWord ++ tailWord_535965) baseStart_535965 baseEnd_535965 := by
    simpa [prefixWord, tailWord_535965, baseEnd_535965] using wordTrace_append hprefix tailTrace_535965
  have hstable : (prefixWord ++ tailWord_535965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_535965).length < 2 ^ (prefixWord ++ tailWord_535965).sum := by decide
  have hdescent : baseEnd_535965 < baseStart_535965 := by decide
  rcases family_descends (prefixWord ++ tailWord_535965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536020 : List Nat := [2, 4, 1, 2, 3, 1, 1, 4, 2]
def baseStart_536020 : Nat := 118140960795 + 536020 * 2 ^ 59
def prefixEnd_536020 : Nat := 4983230072969 + 3 ^ 40 * 536020 * 2
def baseEnd_536020 : Nat := 244654133709420491542129

theorem tailTrace_536020 : CollatzResearch.WordTrace tailWord_536020 prefixEnd_536020 244654133709420491542129 := by
  unfold tailWord_536020
  simp only [CollatzResearch.WordTrace]
  refine ⟨9775127759049279886422757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13033503678732373181897009 9775127759049279886422757)
  ·
    refine ⟨1832836454821739978704267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9775127759049279886422757 1832836454821739978704267)
    ·
      refine ⟨2749254682232609968056401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1832836454821739978704267 2749254682232609968056401)
      ·
        refine ⟨2061941011674457476042301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2749254682232609968056401 2061941011674457476042301)
        ·
          refine ⟨773227879377921553515863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2061941011674457476042301 773227879377921553515863)
          ·
            refine ⟨1159841819066882330273795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773227879377921553515863 1159841819066882330273795)
            ·
              refine ⟨1739762728600323495410693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1159841819066882330273795 1739762728600323495410693)
              ·
                refine ⟨326205511612560655389505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1739762728600323495410693 326205511612560655389505)
                ·
                  refine ⟨244654133709420491542129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326205511612560655389505 244654133709420491542129)
                  ·
                    rfl

theorem cell20_536020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_536020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536020 prefixEnd_536020 := by exact prefixLift 536020
  have htrace : WordTrace (prefixWord ++ tailWord_536020) baseStart_536020 baseEnd_536020 := by
    simpa [prefixWord, tailWord_536020, baseEnd_536020] using wordTrace_append hprefix tailTrace_536020
  have hstable : (prefixWord ++ tailWord_536020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536020).length < 2 ^ (prefixWord ++ tailWord_536020).sum := by decide
  have hdescent : baseEnd_536020 < baseStart_536020 := by decide
  rcases family_descends (prefixWord ++ tailWord_536020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536059 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 7]
def baseStart_536059 : Nat := 118140960795 + 536059 * 2 ^ 59
def prefixEnd_536059 : Nat := 4983230072969 + 3 ^ 40 * 536059 * 2
def baseEnd_536059 : Nat := 244671934372109689241969

theorem tailTrace_536059 : CollatzResearch.WordTrace tailWord_536059 prefixEnd_536059 244671934372109689241969 := by
  unfold tailWord_536059
  simp only [CollatzResearch.WordTrace]
  refine ⟨19551677964957269433515231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13034451976638179622343487 19551677964957269433515231)
  ·
    refine ⟨29327516947435904150272847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19551677964957269433515231 29327516947435904150272847)
    ·
      refine ⟨43991275421153856225409271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29327516947435904150272847 43991275421153856225409271)
      ·
        refine ⟨65986913131730784338113907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43991275421153856225409271 65986913131730784338113907)
        ·
          refine ⟨98980369697596176507170861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65986913131730784338113907 98980369697596176507170861)
          ·
            refine ⟨37117638636598566190189073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 98980369697596176507170861 37117638636598566190189073)
            ·
              refine ⟨27838228977448924642641805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37117638636598566190189073 27838228977448924642641805)
              ·
                refine ⟨10439335866543346740990677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27838228977448924642641805 10439335866543346740990677)
                ·
                  refine ⟨244671934372109689241969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10439335866543346740990677 244671934372109689241969)
                  ·
                    rfl

theorem cell20_536059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_536059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536059 prefixEnd_536059 := by exact prefixLift 536059
  have htrace : WordTrace (prefixWord ++ tailWord_536059) baseStart_536059 baseEnd_536059 := by
    simpa [prefixWord, tailWord_536059, baseEnd_536059] using wordTrace_append hprefix tailTrace_536059
  have hstable : (prefixWord ++ tailWord_536059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536059).length < 2 ^ (prefixWord ++ tailWord_536059).sum := by decide
  have hdescent : baseEnd_536059 < baseStart_536059 := by decide
  rcases family_descends (prefixWord ++ tailWord_536059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536083 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 4]
def baseStart_536083 : Nat := 118140960795 + 536083 * 2 ^ 59
def prefixEnd_536083 : Nat := 4983230072969 + 3 ^ 40 * 536083 * 2
def baseEnd_536083 : Nat := 244682888626072272441871

theorem tailTrace_536083 : CollatzResearch.WordTrace tailWord_536083 prefixEnd_536083 244682888626072272441871 := by
  unfold tailWord_536083
  simp only [CollatzResearch.WordTrace]
  refine ⟨19552553316870321532388903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13035035544580214354925935 19552553316870321532388903)
  ·
    refine ⟨29328829975305482298583355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19552553316870321532388903 29328829975305482298583355)
    ·
      refine ⟨43993244962958223447875033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29328829975305482298583355 43993244962958223447875033)
      ·
        refine ⟨32994933722218667585906275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43993244962958223447875033 32994933722218667585906275)
        ·
          refine ⟨49492400583328001378859413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32994933722218667585906275 49492400583328001378859413)
          ·
            refine ⟨2319956277343500064634035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49492400583328001378859413 2319956277343500064634035)
            ·
              refine ⟨3479934416015250096951053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2319956277343500064634035 3479934416015250096951053)
              ·
                refine ⟨1304975406005718786356645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3479934416015250096951053 1304975406005718786356645)
                ·
                  refine ⟨244682888626072272441871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1304975406005718786356645 244682888626072272441871)
                  ·
                    rfl

theorem cell20_536083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_536083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536083 prefixEnd_536083 := by exact prefixLift 536083
  have htrace : WordTrace (prefixWord ++ tailWord_536083) baseStart_536083 baseEnd_536083 := by
    simpa [prefixWord, tailWord_536083, baseEnd_536083] using wordTrace_append hprefix tailTrace_536083
  have hstable : (prefixWord ++ tailWord_536083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536083).length < 2 ^ (prefixWord ++ tailWord_536083).sum := by decide
  have hdescent : baseEnd_536083 < baseStart_536083 := by decide
  rcases family_descends (prefixWord ++ tailWord_536083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536090 : List Nat := [3, 1, 1, 3, 1, 1, 1, 9]
def baseStart_536090 : Nat := 118140960795 + 536090 * 2 ^ 59
def prefixEnd_536090 : Nat := 4983230072969 + 3 ^ 40 * 536090 * 2
def baseEnd_536090 : Nat := 81562027872270453069503

theorem tailTrace_536090 : CollatzResearch.WordTrace tailWord_536090 prefixEnd_536090 81562027872270453069503 := by
  unfold tailWord_536090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4888202156961240431973431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13035205751896641151929149 4888202156961240431973431)
  ·
    refine ⟨7332303235441860647960147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4888202156961240431973431 7332303235441860647960147)
    ·
      refine ⟨10998454853162790971940221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7332303235441860647960147 10998454853162790971940221)
      ·
        refine ⟨4124420569936046614477583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10998454853162790971940221 4124420569936046614477583)
        ·
          refine ⟨6186630854904069921716375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4124420569936046614477583 6186630854904069921716375)
          ·
            refine ⟨9279946282356104882574563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6186630854904069921716375 9279946282356104882574563)
            ·
              refine ⟨13919919423534157323861845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9279946282356104882574563 13919919423534157323861845)
              ·
                refine ⟨81562027872270453069503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13919919423534157323861845 81562027872270453069503)
                ·
                  rfl

theorem cell20_536090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_536090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536090 prefixEnd_536090 := by exact prefixLift 536090
  have htrace : WordTrace (prefixWord ++ tailWord_536090) baseStart_536090 baseEnd_536090 := by
    simpa [prefixWord, tailWord_536090, baseEnd_536090] using wordTrace_append hprefix tailTrace_536090
  have hstable : (prefixWord ++ tailWord_536090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536090).length < 2 ^ (prefixWord ++ tailWord_536090).sum := by decide
  have hdescent : baseEnd_536090 < baseStart_536090 := by decide
  rcases family_descends (prefixWord ++ tailWord_536090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536117 : List Nat := [1, 3, 3, 1, 1, 3, 3, 3, 2]
def baseStart_536117 : Nat := 118140960795 + 536117 * 2 ^ 59
def prefixEnd_536117 : Nat := 4983230072969 + 3 ^ 40 * 536117 * 2
def baseEnd_536117 : Nat := 244698407152519265308399

theorem tailTrace_536117 : CollatzResearch.WordTrace tailWord_536117 prefixEnd_536117 244698407152519265308399 := by
  unfold tailWord_536117
  simp only [CollatzResearch.WordTrace]
  refine ⟨19553793398747145339126605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13035862265831430226084403 19553793398747145339126605)
  ·
    refine ⟨7332672524530179502172477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19553793398747145339126605 7332672524530179502172477)
    ·
      refine ⟨2749752196698817313314679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7332672524530179502172477 2749752196698817313314679)
      ·
        refine ⟨4124628295048225969972019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2749752196698817313314679 4124628295048225969972019)
        ·
          refine ⟨6186942442572338954958029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4124628295048225969972019 6186942442572338954958029)
          ·
            refine ⟨2320103415964627108109261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6186942442572338954958029 2320103415964627108109261)
            ·
              refine ⟨870038780986735165540973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2320103415964627108109261 870038780986735165540973)
              ·
                refine ⟨326264542870025687077865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 870038780986735165540973 326264542870025687077865)
                ·
                  refine ⟨244698407152519265308399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326264542870025687077865 244698407152519265308399)
                  ·
                    rfl

theorem cell20_536117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_536117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536117 prefixEnd_536117 := by exact prefixLift 536117
  have htrace : WordTrace (prefixWord ++ tailWord_536117) baseStart_536117 baseEnd_536117 := by
    simpa [prefixWord, tailWord_536117, baseEnd_536117] using wordTrace_append hprefix tailTrace_536117
  have hstable : (prefixWord ++ tailWord_536117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536117).length < 2 ^ (prefixWord ++ tailWord_536117).sum := by decide
  have hdescent : baseEnd_536117 < baseStart_536117 := by decide
  rcases family_descends (prefixWord ++ tailWord_536117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536124 : List Nat := [2, 2, 2, 2, 5, 1, 6]
def baseStart_536124 : Nat := 118140960795 + 536124 * 2 ^ 59
def prefixEnd_536124 : Nat := 4983230072969 + 3 ^ 40 * 536124 * 2
def baseEnd_536124 : Nat := 27189066904806483563893

theorem tailTrace_536124 : CollatzResearch.WordTrace tailWord_536124 prefixEnd_536124 27189066904806483563893 := by
  unfold tailWord_536124
  simp only [CollatzResearch.WordTrace]
  refine ⟨9777024354860892767315713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13036032473147857023087617 9777024354860892767315713)
  ·
    refine ⟨7332768266145669575486785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9777024354860892767315713 7332768266145669575486785)
    ·
      refine ⟨5499576199609252181615089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7332768266145669575486785 5499576199609252181615089)
      ·
        refine ⟨4124682149706939136211317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5499576199609252181615089 4124682149706939136211317)
        ·
          refine ⟨386688951535025544019811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4124682149706939136211317 386688951535025544019811)
          ·
            refine ⟨580033427302538316029717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386688951535025544019811 580033427302538316029717)
            ·
              refine ⟨27189066904806483563893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 580033427302538316029717 27189066904806483563893)
              ·
                rfl

theorem cell20_536124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 6].length) (baseStart_536124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536124 prefixEnd_536124 := by exact prefixLift 536124
  have htrace : WordTrace (prefixWord ++ tailWord_536124) baseStart_536124 baseEnd_536124 := by
    simpa [prefixWord, tailWord_536124, baseEnd_536124] using wordTrace_append hprefix tailTrace_536124
  have hstable : (prefixWord ++ tailWord_536124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536124).length < 2 ^ (prefixWord ++ tailWord_536124).sum := by decide
  have hdescent : baseEnd_536124 < baseStart_536124 := by decide
  rcases family_descends (prefixWord ++ tailWord_536124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536193 : List Nat := [1, 2, 4, 2, 1, 3, 1, 4, 2]
def baseStart_536193 : Nat := 118140960795 + 536193 * 2 ^ 59
def prefixEnd_536193 : Nat := 4983230072969 + 3 ^ 40 * 536193 * 2
def baseEnd_536193 : Nat := 244733095623400778774755

theorem tailTrace_536193 : CollatzResearch.WordTrace tailWord_536193 prefixEnd_536193 244733095623400778774755 := by
  unfold tailWord_536193
  simp only [CollatzResearch.WordTrace]
  refine ⟨19556565346471810318893233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13037710230981206879262155 19556565346471810318893233)
  ·
    refine ⟨14667424009853857739169925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19556565346471810318893233 14667424009853857739169925)
    ·
      refine ⟨2750142001847598326094361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14667424009853857739169925 2750142001847598326094361)
      ·
        refine ⟨2062606501385698744570771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2750142001847598326094361 2062606501385698744570771)
        ·
          refine ⟨3093909752078548116856157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062606501385698744570771 3093909752078548116856157)
          ·
            refine ⟨1160216157029455543821059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3093909752078548116856157 1160216157029455543821059)
            ·
              refine ⟨1740324235544183315731589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160216157029455543821059 1740324235544183315731589)
              ·
                refine ⟨326310794164534371699673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1740324235544183315731589 326310794164534371699673)
                ·
                  refine ⟨244733095623400778774755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326310794164534371699673 244733095623400778774755)
                  ·
                    rfl

theorem cell20_536193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 2].length) (baseStart_536193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536193 prefixEnd_536193 := by exact prefixLift 536193
  have htrace : WordTrace (prefixWord ++ tailWord_536193) baseStart_536193 baseEnd_536193 := by
    simpa [prefixWord, tailWord_536193, baseEnd_536193] using wordTrace_append hprefix tailTrace_536193
  have hstable : (prefixWord ++ tailWord_536193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536193).length < 2 ^ (prefixWord ++ tailWord_536193).sum := by decide
  have hdescent : baseEnd_536193 < baseStart_536193 := by decide
  rcases family_descends (prefixWord ++ tailWord_536193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536197 : List Nat := [1, 3, 1, 1, 4, 1, 2, 3, 4]
def baseStart_536197 : Nat := 118140960795 + 536197 * 2 ^ 59
def prefixEnd_536197 : Nat := 4983230072969 + 3 ^ 40 * 536197 * 2
def baseEnd_536197 : Nat := 244734921332394542641405

theorem tailTrace_536197 : CollatzResearch.WordTrace tailWord_536197 prefixEnd_536197 244734921332394542641405 := by
  unfold tailWord_536197
  simp only [CollatzResearch.WordTrace]
  refine ⟨19556711238457319002038845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13037807492304879334692563 19556711238457319002038845)
  ·
    refine ⟨7333766714421494625764567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19556711238457319002038845 7333766714421494625764567)
    ·
      refine ⟨11000650071632241938646851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7333766714421494625764567 11000650071632241938646851)
      ·
        refine ⟨16500975107448362907970277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11000650071632241938646851 16500975107448362907970277)
        ·
          refine ⟨3093932832646568045244427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16500975107448362907970277 3093932832646568045244427)
          ·
            refine ⟨4640899248969852067866641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3093932832646568045244427 4640899248969852067866641)
            ·
              refine ⟨3480674436727389050899981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4640899248969852067866641 3480674436727389050899981)
              ·
                refine ⟨1305252913772770894087493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3480674436727389050899981 1305252913772770894087493)
                ·
                  refine ⟨244734921332394542641405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1305252913772770894087493 244734921332394542641405)
                  ·
                    rfl

theorem cell20_536197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_536197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536197 prefixEnd_536197 := by exact prefixLift 536197
  have htrace : WordTrace (prefixWord ++ tailWord_536197) baseStart_536197 baseEnd_536197 := by
    simpa [prefixWord, tailWord_536197, baseEnd_536197] using wordTrace_append hprefix tailTrace_536197
  have hstable : (prefixWord ++ tailWord_536197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536197).length < 2 ^ (prefixWord ++ tailWord_536197).sum := by decide
  have hdescent : baseEnd_536197 < baseStart_536197 := by decide
  rcases family_descends (prefixWord ++ tailWord_536197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536238 : List Nat := [4, 1, 4, 1, 2, 1, 7]
def baseStart_536238 : Nat := 118140960795 + 536238 * 2 ^ 59
def prefixEnd_536238 : Nat := 4983230072969 + 3 ^ 40 * 536238 * 2
def baseEnd_536238 : Nat := 27194848316620069141619

theorem tailTrace_536238 : CollatzResearch.WordTrace tailWord_536238 prefixEnd_536238 27194848316620069141619 := by
  unfold tailWord_536238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2444775828913597875535171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13038804420872522002854245 2444775828913597875535171)
  ·
    refine ⟨3667163743370396813302757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2444775828913597875535171 3667163743370396813302757)
    ·
      refine ⟨687593201881949402494267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3667163743370396813302757 687593201881949402494267)
      ·
        refine ⟨1031389802822924103741401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687593201881949402494267 1031389802822924103741401)
        ·
          refine ⟨773542352117193077806051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1031389802822924103741401 773542352117193077806051)
          ·
            refine ⟨1160313528175789616709077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773542352117193077806051 1160313528175789616709077)
            ·
              refine ⟨27194848316620069141619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1160313528175789616709077 27194848316620069141619)
              ·
                rfl

theorem cell20_536238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 7].length) (baseStart_536238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536238 prefixEnd_536238 := by exact prefixLift 536238
  have htrace : WordTrace (prefixWord ++ tailWord_536238) baseStart_536238 baseEnd_536238 := by
    simpa [prefixWord, tailWord_536238, baseEnd_536238] using wordTrace_append hprefix tailTrace_536238
  have hstable : (prefixWord ++ tailWord_536238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536238).length < 2 ^ (prefixWord ++ tailWord_536238).sum := by decide
  have hdescent : baseEnd_536238 < baseStart_536238 := by decide
  rcases family_descends (prefixWord ++ tailWord_536238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536245 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 5]
def baseStart_536245 : Nat := 118140960795 + 536245 * 2 ^ 59
def prefixEnd_536245 : Nat := 4983230072969 + 3 ^ 40 * 536245 * 2
def baseEnd_536245 : Nat := 244756829840319709041209

theorem tailTrace_536245 : CollatzResearch.WordTrace tailWord_536245 prefixEnd_536245 244756829840319709041209 := by
  unfold tailWord_536245
  simp only [CollatzResearch.WordTrace]
  refine ⟨19558461942283423199786189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13038974628188948799857459 19558461942283423199786189)
  ·
    refine ⟨7334423228356283699919821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19558461942283423199786189 7334423228356283699919821)
    ·
      refine ⟨2750408710633606387469933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7334423228356283699919821 2750408710633606387469933)
      ·
        refine ⟨1031403266487602395301225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2750408710633606387469933 1031403266487602395301225)
        ·
          refine ⟨773552449865701796475919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1031403266487602395301225 773552449865701796475919)
          ·
            refine ⟨1160328674798552694713879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773552449865701796475919 1160328674798552694713879)
            ·
              refine ⟨1740493012197829042070819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160328674798552694713879 1740493012197829042070819)
              ·
                refine ⟨2610739518296743563106229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1740493012197829042070819 2610739518296743563106229)
                ·
                  refine ⟨244756829840319709041209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2610739518296743563106229 244756829840319709041209)
                  ·
                    rfl

theorem cell20_536245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_536245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536245 prefixEnd_536245 := by exact prefixLift 536245
  have htrace : WordTrace (prefixWord ++ tailWord_536245) baseStart_536245 baseEnd_536245 := by
    simpa [prefixWord, tailWord_536245, baseEnd_536245] using wordTrace_append hprefix tailTrace_536245
  have hstable : (prefixWord ++ tailWord_536245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536245).length < 2 ^ (prefixWord ++ tailWord_536245).sum := by decide
  have hdescent : baseEnd_536245 < baseStart_536245 := by decide
  rcases family_descends (prefixWord ++ tailWord_536245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536252 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 4]
def baseStart_536252 : Nat := 118140960795 + 536252 * 2 ^ 59
def prefixEnd_536252 : Nat := 4983230072969 + 3 ^ 40 * 536252 * 2
def baseEnd_536252 : Nat := 244760024831058795807847

theorem tailTrace_536252 : CollatzResearch.WordTrace tailWord_536252 prefixEnd_536252 244760024831058795807847 := by
  unfold tailWord_536252
  simp only [CollatzResearch.WordTrace]
  refine ⟨9779358626629031697645505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13039144835505375596860673 9779358626629031697645505)
  ·
    refine ⟨7334518969971773773234129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9779358626629031697645505 7334518969971773773234129)
    ·
      refine ⟨5500889227478830329925597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7334518969971773773234129 5500889227478830329925597)
      ·
        refine ⟨2062833460304561373722099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5500889227478830329925597 2062833460304561373722099)
        ·
          refine ⟨3094250190456842060583149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062833460304561373722099 3094250190456842060583149)
          ·
            refine ⟨1160343821421315772718681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3094250190456842060583149 1160343821421315772718681)
            ·
              refine ⟨870257866065986829539011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1160343821421315772718681 870257866065986829539011)
              ·
                refine ⟨1305386799098980244308517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870257866065986829539011 1305386799098980244308517)
                ·
                  refine ⟨244760024831058795807847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1305386799098980244308517 244760024831058795807847)
                  ·
                    rfl

theorem cell20_536252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_536252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536252 prefixEnd_536252 := by exact prefixLift 536252
  have htrace : WordTrace (prefixWord ++ tailWord_536252) baseStart_536252 baseEnd_536252 := by
    simpa [prefixWord, tailWord_536252, baseEnd_536252] using wordTrace_append hprefix tailTrace_536252
  have hstable : (prefixWord ++ tailWord_536252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536252).length < 2 ^ (prefixWord ++ tailWord_536252).sum := by decide
  have hdescent : baseEnd_536252 < baseStart_536252 := by decide
  rcases family_descends (prefixWord ++ tailWord_536252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536269 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 4]
def baseStart_536269 : Nat := 118140960795 + 536269 * 2 ^ 59
def prefixEnd_536269 : Nat := 4983230072969 + 3 ^ 40 * 536269 * 2
def baseEnd_536269 : Nat := 244767784094282292241111

theorem tailTrace_536269 : CollatzResearch.WordTrace tailWord_536269 prefixEnd_536269 244767784094282292241111 := by
  unfold tailWord_536269
  simp only [CollatzResearch.WordTrace]
  refine ⟨19559337294196475298659861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13039558196130983532439907 19559337294196475298659861)
  ·
    refine ⟨916843935665459779624681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19559337294196475298659861 916843935665459779624681)
    ·
      refine ⟨687632951749094834718511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 916843935665459779624681 687632951749094834718511)
      ·
        refine ⟨1031449427623642252077767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687632951749094834718511 1031449427623642252077767)
        ·
          refine ⟨1547174141435463378116651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1031449427623642252077767 1547174141435463378116651)
          ·
            refine ⟨2320761212153195067174977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1547174141435463378116651 2320761212153195067174977)
            ·
              refine ⟨1740570909114896300381233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2320761212153195067174977 1740570909114896300381233)
              ·
                refine ⟨1305428181836172225285925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1740570909114896300381233 1305428181836172225285925)
                ·
                  refine ⟨244767784094282292241111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1305428181836172225285925 244767784094282292241111)
                  ·
                    rfl

theorem cell20_536269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_536269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536269 prefixEnd_536269 := by exact prefixLift 536269
  have htrace : WordTrace (prefixWord ++ tailWord_536269) baseStart_536269 baseEnd_536269 := by
    simpa [prefixWord, tailWord_536269, baseEnd_536269] using wordTrace_append hprefix tailTrace_536269
  have hstable : (prefixWord ++ tailWord_536269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536269).length < 2 ^ (prefixWord ++ tailWord_536269).sum := by decide
  have hdescent : baseEnd_536269 < baseStart_536269 := by decide
  rcases family_descends (prefixWord ++ tailWord_536269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536273 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 4]
def baseStart_536273 : Nat := 118140960795 + 536273 * 2 ^ 59
def prefixEnd_536273 : Nat := 4983230072969 + 3 ^ 40 * 536273 * 2
def baseEnd_536273 : Nat := 244769609803276056107761

theorem tailTrace_536273 : CollatzResearch.WordTrace tailWord_536273 prefixEnd_536273 244769609803276056107761 := by
  unfold tailWord_536273
  simp only [CollatzResearch.WordTrace]
  refine ⟨19559483186181983981805473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13039655457454655987870315 19559483186181983981805473)
  ·
    refine ⟨14669612389636487986354105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19559483186181983981805473 14669612389636487986354105)
    ·
      refine ⟨11002209292227365989765579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14669612389636487986354105 11002209292227365989765579)
      ·
        refine ⟨16503313938341048984648369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11002209292227365989765579 16503313938341048984648369)
        ·
          refine ⟨12377485453755786738486277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16503313938341048984648369 12377485453755786738486277)
          ·
            refine ⟨2320778522579210013466177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12377485453755786738486277 2320778522579210013466177)
            ·
              refine ⟨1740583891934407510099633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2320778522579210013466177 1740583891934407510099633)
              ·
                refine ⟨1305437918950805632574725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1740583891934407510099633 1305437918950805632574725)
                ·
                  refine ⟨244769609803276056107761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1305437918950805632574725 244769609803276056107761)
                  ·
                    rfl

theorem cell20_536273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_536273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536273 prefixEnd_536273 := by exact prefixLift 536273
  have htrace : WordTrace (prefixWord ++ tailWord_536273) baseStart_536273 baseEnd_536273 := by
    simpa [prefixWord, tailWord_536273, baseEnd_536273] using wordTrace_append hprefix tailTrace_536273
  have hstable : (prefixWord ++ tailWord_536273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536273).length < 2 ^ (prefixWord ++ tailWord_536273).sum := by decide
  have hdescent : baseEnd_536273 < baseStart_536273 := by decide
  rcases family_descends (prefixWord ++ tailWord_536273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536276 : List Nat := [2, 4, 1, 3, 1, 1, 4, 4]
def baseStart_536276 : Nat := 118140960795 + 536276 * 2 ^ 59
def prefixEnd_536276 : Nat := 4983230072969 + 3 ^ 40 * 536276 * 2
def baseEnd_536276 : Nat := 81590326361673793002583

theorem tailTrace_536276 : CollatzResearch.WordTrace tailWord_536276 prefixEnd_536276 81590326361673793002583 := by
  unfold tailWord_536276
  simp only [CollatzResearch.WordTrace]
  refine ⟨9779796302585557747082341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13039728403447410329443121 9779796302585557747082341)
  ·
    refine ⟨1833711806734792077577939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9779796302585557747082341 1833711806734792077577939)
    ·
      refine ⟨2750567710102188116366909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1833711806734792077577939 2750567710102188116366909)
      ·
        refine ⟨1031462891288320543637591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2750567710102188116366909 1031462891288320543637591)
        ·
          refine ⟨1547194336932480815456387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1031462891288320543637591 1547194336932480815456387)
          ·
            refine ⟨2320791505398721223184581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1547194336932480815456387 2320791505398721223184581)
            ·
              refine ⟨435148407262260229347109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2320791505398721223184581 435148407262260229347109)
              ·
                refine ⟨81590326361673793002583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 435148407262260229347109 81590326361673793002583)
                ·
                  rfl

theorem cell20_536276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_536276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536276 prefixEnd_536276 := by exact prefixLift 536276
  have htrace : WordTrace (prefixWord ++ tailWord_536276) baseStart_536276 baseEnd_536276 := by
    simpa [prefixWord, tailWord_536276, baseEnd_536276] using wordTrace_append hprefix tailTrace_536276
  have hstable : (prefixWord ++ tailWord_536276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536276).length < 2 ^ (prefixWord ++ tailWord_536276).sum := by decide
  have hdescent : baseEnd_536276 < baseStart_536276 := by decide
  rcases family_descends (prefixWord ++ tailWord_536276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536280 : List Nat := [2, 1, 2, 2, 3, 1, 3, 6]
def baseStart_536280 : Nat := 118140960795 + 536280 * 2 ^ 59
def prefixEnd_536280 : Nat := 4983230072969 + 3 ^ 40 * 536280 * 2
def baseEnd_536280 : Nat := 81590934931338380958133

theorem tailTrace_536280 : CollatzResearch.WordTrace tailWord_536280 prefixEnd_536280 81590934931338380958133 := by
  unfold tailWord_536280
  simp only [CollatzResearch.WordTrace]
  refine ⟨9779869248578312088655147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13039825664771082784873529 9779869248578312088655147)
  ·
    refine ⟨14669803872867468132982721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9779869248578312088655147 14669803872867468132982721)
    ·
      refine ⟨11002352904650601099737041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14669803872867468132982721 11002352904650601099737041)
      ·
        refine ⟨8251764678487950824802781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11002352904650601099737041 8251764678487950824802781)
        ·
          refine ⟨3094411754432981559301043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8251764678487950824802781 3094411754432981559301043)
          ·
            refine ⟨4641617631649472338951565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3094411754432981559301043 4641617631649472338951565)
            ·
              refine ⟨1740606611868552127106837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4641617631649472338951565 1740606611868552127106837)
              ·
                refine ⟨81590934931338380958133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1740606611868552127106837 81590934931338380958133)
                ·
                  rfl

theorem cell20_536280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_536280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536280 prefixEnd_536280 := by exact prefixLift 536280
  have htrace : WordTrace (prefixWord ++ tailWord_536280) baseStart_536280 baseEnd_536280 := by
    simpa [prefixWord, tailWord_536280, baseEnd_536280] using wordTrace_append hprefix tailTrace_536280
  have hstable : (prefixWord ++ tailWord_536280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536280).length < 2 ^ (prefixWord ++ tailWord_536280).sum := by decide
  have hdescent : baseEnd_536280 < baseStart_536280 := by decide
  rcases family_descends (prefixWord ++ tailWord_536280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536287 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 7]
def baseStart_536287 : Nat := 118140960795 + 536287 * 2 ^ 59
def prefixEnd_536287 : Nat := 4983230072969 + 3 ^ 40 * 536287 * 2
def baseEnd_536287 : Nat := 244775999784754229641037

theorem tailTrace_536287 : CollatzResearch.WordTrace tailWord_536287 prefixEnd_536287 244775999784754229641037 := by
  unfold tailWord_536287
  simp only [CollatzResearch.WordTrace]
  refine ⟨19559993808131264372815115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13039995872087509581876743 19559993808131264372815115)
  ·
    refine ⟨29339990712196896559222673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19559993808131264372815115 29339990712196896559222673)
    ·
      refine ⟨22004993034147672419417005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29339990712196896559222673 22004993034147672419417005)
      ·
        refine ⟨8251872387805377157281377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22004993034147672419417005 8251872387805377157281377)
        ·
          refine ⟨6188904290854032867961033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8251872387805377157281377 6188904290854032867961033)
          ·
            refine ⟨4641678218140524650970775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6188904290854032867961033 4641678218140524650970775)
            ·
              refine ⟨6962517327210786976456163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4641678218140524650970775 6962517327210786976456163)
              ·
                refine ⟨10443775990816180464684245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6962517327210786976456163 10443775990816180464684245)
                ·
                  refine ⟨244775999784754229641037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10443775990816180464684245 244775999784754229641037)
                  ·
                    rfl

theorem cell20_536287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_536287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536287 prefixEnd_536287 := by exact prefixLift 536287
  have htrace : WordTrace (prefixWord ++ tailWord_536287) baseStart_536287 baseEnd_536287 := by
    simpa [prefixWord, tailWord_536287, baseEnd_536287] using wordTrace_append hprefix tailTrace_536287
  have hstable : (prefixWord ++ tailWord_536287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536287).length < 2 ^ (prefixWord ++ tailWord_536287).sum := by decide
  have hdescent : baseEnd_536287 < baseStart_536287 := by decide
  rcases family_descends (prefixWord ++ tailWord_536287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536311 : List Nat := [1, 1, 3, 1, 1, 1, 7, 1, 4]
def baseStart_536311 : Nat := 118140960795 + 536311 * 2 ^ 59
def prefixEnd_536311 : Nat := 4983230072969 + 3 ^ 40 * 536311 * 2
def baseEnd_536311 : Nat := 244786954038716812840939

theorem tailTrace_536311 : CollatzResearch.WordTrace tailWord_536311 prefixEnd_536311 244786954038716812840939 := by
  unfold tailWord_536311
  simp only [CollatzResearch.WordTrace]
  refine ⟨19560869160044316471688787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13040579440029544314459191 19560869160044316471688787)
  ·
    refine ⟨29341303740066474707533181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19560869160044316471688787 29341303740066474707533181)
    ·
      refine ⟨11002988902524928015324943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29341303740066474707533181 11002988902524928015324943)
      ·
        refine ⟨16504483353787392022987415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11002988902524928015324943 16504483353787392022987415)
        ·
          refine ⟨24756725030681088034481123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16504483353787392022987415 24756725030681088034481123)
          ·
            refine ⟨37135087546021632051721685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24756725030681088034481123 37135087546021632051721685)
            ·
              refine ⟨870353614359882001212227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 37135087546021632051721685 870353614359882001212227)
              ·
                refine ⟨1305530421539823001818341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870353614359882001212227 1305530421539823001818341)
                ·
                  refine ⟨244786954038716812840939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1305530421539823001818341 244786954038716812840939)
                  ·
                    rfl

theorem cell20_536311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_536311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536311 prefixEnd_536311 := by exact prefixLift 536311
  have htrace : WordTrace (prefixWord ++ tailWord_536311) baseStart_536311 baseEnd_536311 := by
    simpa [prefixWord, tailWord_536311, baseEnd_536311] using wordTrace_append hprefix tailTrace_536311
  have hstable : (prefixWord ++ tailWord_536311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536311).length < 2 ^ (prefixWord ++ tailWord_536311).sum := by decide
  have hdescent : baseEnd_536311 < baseStart_536311 := by decide
  rcases family_descends (prefixWord ++ tailWord_536311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536321 : List Nat := [1, 2, 4, 1, 1, 1, 6, 1, 3]
def baseStart_536321 : Nat := 118140960795 + 536321 * 2 ^ 59
def prefixEnd_536321 : Nat := 4983230072969 + 3 ^ 40 * 536321 * 2
def baseEnd_536321 : Nat := 244791518311201222507565

theorem tailTrace_536321 : CollatzResearch.WordTrace tailWord_536321 prefixEnd_536321 244791518311201222507565 := by
  unfold tailWord_536321
  simp only [CollatzResearch.WordTrace]
  refine ⟨19561233890008088179552817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13040822593338725453035211 19561233890008088179552817)
  ·
    refine ⟨14670925417506066134664613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19561233890008088179552817 14670925417506066134664613)
    ·
      refine ⟨2750798515782387400249615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14670925417506066134664613 2750798515782387400249615)
      ·
        refine ⟨4126197773673581100374423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2750798515782387400249615 4126197773673581100374423)
        ·
          refine ⟨6189296660510371650561635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4126197773673581100374423 6189296660510371650561635)
          ·
            refine ⟨9283944990765557475842453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6189296660510371650561635 9283944990765557475842453)
            ·
              refine ⟨435184921442135506680115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9283944990765557475842453 435184921442135506680115)
              ·
                refine ⟨652777382163203260020173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435184921442135506680115 652777382163203260020173)
                ·
                  refine ⟨244791518311201222507565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 652777382163203260020173 244791518311201222507565)
                  ·
                    rfl

theorem cell20_536321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 1, 3].length) (baseStart_536321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536321 prefixEnd_536321 := by exact prefixLift 536321
  have htrace : WordTrace (prefixWord ++ tailWord_536321) baseStart_536321 baseEnd_536321 := by
    simpa [prefixWord, tailWord_536321, baseEnd_536321] using wordTrace_append hprefix tailTrace_536321
  have hstable : (prefixWord ++ tailWord_536321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536321).length < 2 ^ (prefixWord ++ tailWord_536321).sum := by decide
  have hdescent : baseEnd_536321 < baseStart_536321 := by decide
  rcases family_descends (prefixWord ++ tailWord_536321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536356 : List Nat := [2, 3, 1, 3, 2, 9]
def baseStart_536356 : Nat := 118140960795 + 536356 * 2 ^ 59
def prefixEnd_536356 : Nat := 4983230072969 + 3 ^ 40 * 536356 * 2
def baseEnd_536356 : Nat := 9066944194996172457065

theorem tailTrace_536356 : CollatzResearch.WordTrace tailWord_536356 prefixEnd_536356 9066944194996172457065 := by
  unfold tailWord_536356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9781255222440644578538461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13041673629920859438051281 9781255222440644578538461)
  ·
    refine ⟨3667970708415241716951923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9781255222440644578538461 3667970708415241716951923)
    ·
      refine ⟨5501956062622862575427885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3667970708415241716951923 5501956062622862575427885)
      ·
        refine ⟨2063233523483573465785457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5501956062622862575427885 2063233523483573465785457)
        ·
          refine ⟨1547425142612680099339093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2063233523483573465785457 1547425142612680099339093)
          ·
            refine ⟨9066944194996172457065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1547425142612680099339093 9066944194996172457065)
            ·
              rfl

theorem cell20_536356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 9].length) (baseStart_536356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536356 prefixEnd_536356 := by exact prefixLift 536356
  have htrace : WordTrace (prefixWord ++ tailWord_536356) baseStart_536356 baseEnd_536356 := by
    simpa [prefixWord, tailWord_536356, baseEnd_536356] using wordTrace_append hprefix tailTrace_536356
  have hstable : (prefixWord ++ tailWord_536356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536356).length < 2 ^ (prefixWord ++ tailWord_536356).sum := by decide
  have hdescent : baseEnd_536356 < baseStart_536356 := by decide
  rcases family_descends (prefixWord ++ tailWord_536356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536380 : List Nat := [2, 2, 2, 2, 1, 1, 4, 3, 3]
def baseStart_536380 : Nat := 118140960795 + 536380 * 2 ^ 59
def prefixEnd_536380 : Nat := 4983230072969 + 3 ^ 40 * 536380 * 2
def baseEnd_536380 : Nat := 244818447518859239540657

theorem tailTrace_536380 : CollatzResearch.WordTrace tailWord_536380 prefixEnd_536380 244818447518859239540657 := by
  unfold tailWord_536380
  simp only [CollatzResearch.WordTrace]
  refine ⟨9781692898397170627975297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13042257197862894170633729 9781692898397170627975297)
  ·
    refine ⟨7336269673797877970981473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9781692898397170627975297 7336269673797877970981473)
    ·
      refine ⟨5502202255348408478236105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7336269673797877970981473 5502202255348408478236105)
      ·
        refine ⟨4126651691511306358677079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5502202255348408478236105 4126651691511306358677079)
        ·
          refine ⟨6189977537266959538015619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4126651691511306358677079 6189977537266959538015619)
          ·
            refine ⟨9284966305900439307023429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6189977537266959538015619 9284966305900439307023429)
            ·
              refine ⟨1740931182356332370066893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9284966305900439307023429 1740931182356332370066893)
              ·
                refine ⟨652849193383624638775085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1740931182356332370066893 652849193383624638775085)
                ·
                  refine ⟨244818447518859239540657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 652849193383624638775085 244818447518859239540657)
                  ·
                    rfl

theorem cell20_536380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_536380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536380 prefixEnd_536380 := by exact prefixLift 536380
  have htrace : WordTrace (prefixWord ++ tailWord_536380) baseStart_536380 baseEnd_536380 := by
    simpa [prefixWord, tailWord_536380, baseEnd_536380] using wordTrace_append hprefix tailTrace_536380
  have hstable : (prefixWord ++ tailWord_536380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536380).length < 2 ^ (prefixWord ++ tailWord_536380).sum := by decide
  have hdescent : baseEnd_536380 < baseStart_536380 := by decide
  rcases family_descends (prefixWord ++ tailWord_536380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536387 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 4]
def baseStart_536387 : Nat := 118140960795 + 536387 * 2 ^ 59
def prefixEnd_536387 : Nat := 4983230072969 + 3 ^ 40 * 536387 * 2
def baseEnd_536387 : Nat := 244821642509598326307295

theorem tailTrace_536387 : CollatzResearch.WordTrace tailWord_536387 prefixEnd_536387 244821642509598326307295 := by
  unfold tailWord_536387
  simp only [CollatzResearch.WordTrace]
  refine ⟨19563641107768981451455415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13042427405179320967636943 19563641107768981451455415)
  ·
    refine ⟨29345461661653472177183123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19563641107768981451455415 29345461661653472177183123)
    ·
      refine ⟨44018192492480208265774685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29345461661653472177183123 44018192492480208265774685)
      ·
        refine ⟨16506822184680078099665507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44018192492480208265774685 16506822184680078099665507)
        ·
          refine ⟨24760233277020117149498261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16506822184680078099665507 24760233277020117149498261)
          ·
            refine ⟨1160635934860317991382731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24760233277020117149498261 1160635934860317991382731)
            ·
              refine ⟨1740953902290476987074097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160635934860317991382731 1740953902290476987074097)
              ·
                refine ⟨1305715426717857740305573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1740953902290476987074097 1305715426717857740305573)
                ·
                  refine ⟨244821642509598326307295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1305715426717857740305573 244821642509598326307295)
                  ·
                    rfl

theorem cell20_536387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 4].length) (baseStart_536387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536387 prefixEnd_536387 := by exact prefixLift 536387
  have htrace : WordTrace (prefixWord ++ tailWord_536387) baseStart_536387 baseEnd_536387 := by
    simpa [prefixWord, tailWord_536387, baseEnd_536387] using wordTrace_append hprefix tailTrace_536387
  have hstable : (prefixWord ++ tailWord_536387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536387).length < 2 ^ (prefixWord ++ tailWord_536387).sum := by decide
  have hdescent : baseEnd_536387 < baseStart_536387 := by decide
  rcases family_descends (prefixWord ++ tailWord_536387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536476 : List Nat := [2, 2, 3, 3, 1, 2, 3, 2, 2]
def baseStart_536476 : Nat := 118140960795 + 536476 * 2 ^ 59
def prefixEnd_536476 : Nat := 4983230072969 + 3 ^ 40 * 536476 * 2
def baseEnd_536476 : Nat := 244862264534709572340265

theorem tailTrace_536476 : CollatzResearch.WordTrace tailWord_536476 prefixEnd_536476 244862264534709572340265 := by
  unfold tailWord_536476
  simp only [CollatzResearch.WordTrace]
  refine ⟨9783443602223274825722641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13044591469631033100963521 9783443602223274825722641)
  ·
    refine ⟨7337582701667456119291981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9783443602223274825722641 7337582701667456119291981)
    ·
      refine ⟨2751593513125296044734493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7337582701667456119291981 2751593513125296044734493)
      ·
        refine ⟨1031847567421986016775435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2751593513125296044734493 1031847567421986016775435)
        ·
          refine ⟨1547771351132979025163153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1031847567421986016775435 1547771351132979025163153)
          ·
            refine ⟨1160828513349734268872365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1547771351132979025163153 1160828513349734268872365)
            ·
              refine ⟨435310692506150350827137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1160828513349734268872365 435310692506150350827137)
              ·
                refine ⟨326483019379612763120353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435310692506150350827137 326483019379612763120353)
                ·
                  refine ⟨244862264534709572340265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326483019379612763120353 244862264534709572340265)
                  ·
                    rfl

theorem cell20_536476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_536476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536476 prefixEnd_536476 := by exact prefixLift 536476
  have htrace : WordTrace (prefixWord ++ tailWord_536476) baseStart_536476 baseEnd_536476 := by
    simpa [prefixWord, tailWord_536476, baseEnd_536476] using wordTrace_append hprefix tailTrace_536476
  have hstable : (prefixWord ++ tailWord_536476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536476).length < 2 ^ (prefixWord ++ tailWord_536476).sum := by decide
  have hdescent : baseEnd_536476 < baseStart_536476 := by decide
  rcases family_descends (prefixWord ++ tailWord_536476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536487 : List Nat := [1, 1, 6, 1, 2, 2, 2, 5]
def baseStart_536487 : Nat := 118140960795 + 536487 * 2 ^ 59
def prefixEnd_536487 : Nat := 4983230072969 + 3 ^ 40 * 536487 * 2
def baseEnd_536487 : Nat := 81622428411480807657851

theorem tailTrace_536487 : CollatzResearch.WordTrace tailWord_536487 prefixEnd_536487 81622428411480807657851 := by
  unfold tailWord_536487
  simp only [CollatzResearch.WordTrace]
  refine ⟨19567288407406698530095715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13044858938271132353397143 19567288407406698530095715)
  ·
    refine ⟨29350932611110047795143573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19567288407406698530095715 29350932611110047795143573)
    ·
      refine ⟨1375824966145783490397355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29350932611110047795143573 1375824966145783490397355)
      ·
        refine ⟨2063737449218675235596033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375824966145783490397355 2063737449218675235596033)
        ·
          refine ⟨1547803086914006426697025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2063737449218675235596033 1547803086914006426697025)
          ·
            refine ⟨1160852315185504820022769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1547803086914006426697025 1160852315185504820022769)
            ·
              refine ⟨870639236389128615017077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1160852315185504820022769 870639236389128615017077)
              ·
                refine ⟨81622428411480807657851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 870639236389128615017077 81622428411480807657851)
                ·
                  rfl

theorem cell20_536487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 5].length) (baseStart_536487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536487 prefixEnd_536487 := by exact prefixLift 536487
  have htrace : WordTrace (prefixWord ++ tailWord_536487) baseStart_536487 baseEnd_536487 := by
    simpa [prefixWord, tailWord_536487, baseEnd_536487] using wordTrace_append hprefix tailTrace_536487
  have hstable : (prefixWord ++ tailWord_536487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536487).length < 2 ^ (prefixWord ++ tailWord_536487).sum := by decide
  have hdescent : baseEnd_536487 < baseStart_536487 := by decide
  rcases family_descends (prefixWord ++ tailWord_536487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536525 : List Nat := [1, 6, 3, 10]
def baseStart_536525 : Nat := 118140960795 + 536525 * 2 ^ 59
def prefixEnd_536525 : Nat := 4983230072969 + 3 ^ 40 * 536525 * 2
def baseEnd_536525 : Nat := 1007755676830794978217

theorem tailTrace_536525 : CollatzResearch.WordTrace tailWord_536525 prefixEnd_536525 1007755676830794978217 := by
  unfold tailWord_536525
  simp only [CollatzResearch.WordTrace]
  refine ⟨19568674381269031019979029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13045782920846020679986019 19568674381269031019979029)
  ·
    refine ⟨917281611621985829061517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19568674381269031019979029 917281611621985829061517)
    ·
      refine ⟨343980604358244685898069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 917281611621985829061517 343980604358244685898069)
      ·
        refine ⟨1007755676830794978217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 343980604358244685898069 1007755676830794978217)
        ·
          rfl

theorem cell20_536525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 10].length) (baseStart_536525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536525 prefixEnd_536525 := by exact prefixLift 536525
  have htrace : WordTrace (prefixWord ++ tailWord_536525) baseStart_536525 baseEnd_536525 := by
    simpa [prefixWord, tailWord_536525, baseEnd_536525] using wordTrace_append hprefix tailTrace_536525
  have hstable : (prefixWord ++ tailWord_536525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536525).length < 2 ^ (prefixWord ++ tailWord_536525).sum := by decide
  have hdescent : baseEnd_536525 < baseStart_536525 := by decide
  rcases family_descends (prefixWord ++ tailWord_536525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536560 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_536560 : Nat := 118140960795 + 536560 * 2 ^ 59
def prefixEnd_536560 : Nat := 4983230072969 + 3 ^ 40 * 536560 * 2
def baseEnd_536560 : Nat := 244900604423578613539921

theorem tailTrace_536560 : CollatzResearch.WordTrace tailWord_536560 prefixEnd_536560 244900604423578613539921 := by
  unfold tailWord_536560
  simp only [CollatzResearch.WordTrace]
  refine ⟨9784975468071115998751567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13046633957428154665002089 9784975468071115998751567)
  ·
    refine ⟨14677463202106673998127351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9784975468071115998751567 14677463202106673998127351)
    ·
      refine ⟨22016194803160010997191027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14677463202106673998127351 22016194803160010997191027)
      ·
        refine ⟨33024292204740016495786541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22016194803160010997191027 33024292204740016495786541)
        ·
          refine ⟨12384109576777506185919953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33024292204740016495786541 12384109576777506185919953)
          ·
            refine ⟨9288082182583129639439965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12384109576777506185919953 9288082182583129639439965)
            ·
              refine ⟨3483030818468673614789987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9288082182583129639439965 3483030818468673614789987)
              ·
                refine ⟨5224546227703010422184981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3483030818468673614789987 5224546227703010422184981)
                ·
                  refine ⟨244900604423578613539921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5224546227703010422184981 244900604423578613539921)
                  ·
                    rfl

theorem cell20_536560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_536560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536560 prefixEnd_536560 := by exact prefixLift 536560
  have htrace : WordTrace (prefixWord ++ tailWord_536560) baseStart_536560 baseEnd_536560 := by
    simpa [prefixWord, tailWord_536560, baseEnd_536560] using wordTrace_append hprefix tailTrace_536560
  have hstable : (prefixWord ++ tailWord_536560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536560).length < 2 ^ (prefixWord ++ tailWord_536560).sum := by decide
  have hdescent : baseEnd_536560 < baseStart_536560 := by decide
  rcases family_descends (prefixWord ++ tailWord_536560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536618 : List Nat := [3, 1, 4, 1, 2, 3, 2, 4]
def baseStart_536618 : Nat := 118140960795 + 536618 * 2 ^ 59
def prefixEnd_536618 : Nat := 4983230072969 + 3 ^ 40 * 536618 * 2
def baseEnd_536618 : Nat := 81642359067996063202117

theorem tailTrace_536618 : CollatzResearch.WordTrace tailWord_536618 prefixEnd_536618 81642359067996063202117 := by
  unfold tailWord_536618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4893016592483026975778627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13048044246621405268743005 4893016592483026975778627)
  ·
    refine ⟨7339524888724540463667941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4893016592483026975778627 7339524888724540463667941)
    ·
      refine ⟨1376160916635851336937739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7339524888724540463667941 1376160916635851336937739)
      ·
        refine ⟨2064241374953777005406609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1376160916635851336937739 2064241374953777005406609)
        ·
          refine ⟨1548181031215332754054957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2064241374953777005406609 1548181031215332754054957)
          ·
            refine ⟨580567886705749782770609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1548181031215332754054957 580567886705749782770609)
            ·
              refine ⟨435425915029312337077957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580567886705749782770609 435425915029312337077957)
              ·
                refine ⟨81642359067996063202117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 435425915029312337077957 81642359067996063202117)
                ·
                  rfl

theorem cell20_536618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_536618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536618 prefixEnd_536618 := by exact prefixLift 536618
  have htrace : WordTrace (prefixWord ++ tailWord_536618) baseStart_536618 baseEnd_536618 := by
    simpa [prefixWord, tailWord_536618, baseEnd_536618] using wordTrace_append hprefix tailTrace_536618
  have hstable : (prefixWord ++ tailWord_536618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536618).length < 2 ^ (prefixWord ++ tailWord_536618).sum := by decide
  have hdescent : baseEnd_536618 < baseStart_536618 := by decide
  rcases family_descends (prefixWord ++ tailWord_536618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536629 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 5]
def baseStart_536629 : Nat := 118140960795 + 536629 * 2 ^ 59
def prefixEnd_536629 : Nat := 4983230072969 + 3 ^ 40 * 536629 * 2
def baseEnd_536629 : Nat := 244932097903721040239639

theorem tailTrace_536629 : CollatzResearch.WordTrace tailWord_536629 prefixEnd_536629 244932097903721040239639 := by
  unfold tailWord_536629
  simp only [CollatzResearch.WordTrace]
  refine ⟨19572467572892256781764941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13048311715261504521176627 19572467572892256781764941)
  ·
    refine ⟨7339675339834596293161853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19572467572892256781764941 7339675339834596293161853)
    ·
      refine ⟨2752378252437973609935695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7339675339834596293161853 2752378252437973609935695)
      ·
        refine ⟨4128567378656960414903543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2752378252437973609935695 4128567378656960414903543)
        ·
          refine ⟨6192851067985440622355315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4128567378656960414903543 6192851067985440622355315)
          ·
            refine ⟨9289276601978160933532973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6192851067985440622355315 9289276601978160933532973)
            ·
              refine ⟨3483478725741810350074865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9289276601978160933532973 3483478725741810350074865)
              ·
                refine ⟨2612609044306357762556149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3483478725741810350074865 2612609044306357762556149)
                ·
                  refine ⟨244932097903721040239639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2612609044306357762556149 244932097903721040239639)
                  ·
                    rfl

theorem cell20_536629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_536629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536629 prefixEnd_536629 := by exact prefixLift 536629
  have htrace : WordTrace (prefixWord ++ tailWord_536629) baseStart_536629 baseEnd_536629 := by
    simpa [prefixWord, tailWord_536629, baseEnd_536629] using wordTrace_append hprefix tailTrace_536629
  have hstable : (prefixWord ++ tailWord_536629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536629).length < 2 ^ (prefixWord ++ tailWord_536629).sum := by decide
  have hdescent : baseEnd_536629 < baseStart_536629 := by decide
  rcases family_descends (prefixWord ++ tailWord_536629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536681 : List Nat := [1, 2, 1, 1, 1, 5, 1, 8]
def baseStart_536681 : Nat := 118140960795 + 536681 * 2 ^ 59
def prefixEnd_536681 : Nat := 4983230072969 + 3 ^ 40 * 536681 * 2
def baseEnd_536681 : Nat := 81651944040213323502031

theorem tailTrace_536681 : CollatzResearch.WordTrace tailWord_536681 prefixEnd_536681 81651944040213323502031 := by
  unfold tailWord_536681
  simp only [CollatzResearch.WordTrace]
  refine ⟨19574364168703869662657897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13049576112469246441771931 19574364168703869662657897)
  ·
    refine ⟨14680773126527902246993423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19574364168703869662657897 14680773126527902246993423)
    ·
      refine ⟨22021159689791853370490135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14680773126527902246993423 22021159689791853370490135)
      ·
        refine ⟨33031739534687780055735203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22021159689791853370490135 33031739534687780055735203)
        ·
          refine ⟨49547609302031670083602805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33031739534687780055735203 49547609302031670083602805)
          ·
            refine ⟨4645088372065469070337763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49547609302031670083602805 4645088372065469070337763)
            ·
              refine ⟨6967632558098203605506645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4645088372065469070337763 6967632558098203605506645)
              ·
                refine ⟨81651944040213323502031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6967632558098203605506645 81651944040213323502031)
                ·
                  rfl

theorem cell20_536681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 8].length) (baseStart_536681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536681 prefixEnd_536681 := by exact prefixLift 536681
  have htrace : WordTrace (prefixWord ++ tailWord_536681) baseStart_536681 baseEnd_536681 := by
    simpa [prefixWord, tailWord_536681, baseEnd_536681] using wordTrace_append hprefix tailTrace_536681
  have hstable : (prefixWord ++ tailWord_536681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536681).length < 2 ^ (prefixWord ++ tailWord_536681).sum := by decide
  have hdescent : baseEnd_536681 < baseStart_536681 := by decide
  rcases family_descends (prefixWord ++ tailWord_536681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536708 : List Nat := [2, 3, 2, 1, 2, 1, 3, 4, 2]
def baseStart_536708 : Nat := 118140960795 + 536708 * 2 ^ 59
def prefixEnd_536708 : Nat := 4983230072969 + 3 ^ 40 * 536708 * 2
def baseEnd_536708 : Nat := 244968155656347876605983

theorem tailTrace_536708 : CollatzResearch.WordTrace tailWord_536708 prefixEnd_536708 244968155656347876605983 := by
  unfold tailWord_536708
  simp only [CollatzResearch.WordTrace]
  refine ⟨9787674469803026636945389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13050232626404035515927185 9787674469803026636945389)
  ·
    refine ⟨3670377926176134988854521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9787674469803026636945389 3670377926176134988854521)
    ·
      refine ⟨2752783444632101241640891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3670377926176134988854521 2752783444632101241640891)
      ·
        refine ⟨4129175166948151862461337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2752783444632101241640891 4129175166948151862461337)
        ·
          refine ⟨3096881375211113896846003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4129175166948151862461337 3096881375211113896846003)
          ·
            refine ⟨4645322062816670845269005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3096881375211113896846003 4645322062816670845269005)
            ·
              refine ⟨1741995773556251566975877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4645322062816670845269005 1741995773556251566975877)
              ·
                refine ⟨326624207541797168807977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1741995773556251566975877 326624207541797168807977)
                ·
                  refine ⟨244968155656347876605983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326624207541797168807977 244968155656347876605983)
                  ·
                    rfl

theorem cell20_536708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_536708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536708 prefixEnd_536708 := by exact prefixLift 536708
  have htrace : WordTrace (prefixWord ++ tailWord_536708) baseStart_536708 baseEnd_536708 := by
    simpa [prefixWord, tailWord_536708, baseEnd_536708] using wordTrace_append hprefix tailTrace_536708
  have hstable : (prefixWord ++ tailWord_536708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536708).length < 2 ^ (prefixWord ++ tailWord_536708).sum := by decide
  have hdescent : baseEnd_536708 < baseStart_536708 := by decide
  rcases family_descends (prefixWord ++ tailWord_536708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536722 : List Nat := [3, 2, 3, 1, 1, 1, 1, 5, 3]
def baseStart_536722 : Nat := 118140960795 + 536722 * 2 ^ 59
def prefixEnd_536722 : Nat := 4983230072969 + 3 ^ 40 * 536722 * 2
def baseEnd_536722 : Nat := 244974545637826050139259

theorem tailTrace_536722 : CollatzResearch.WordTrace tailWord_536722 prefixEnd_536722 244974545637826050139259 := by
  unfold tailWord_536722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4893964890388833416225105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13050573041036889109933613 4893964890388833416225105)
  ·
    refine ⟨3670473667791625062168829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4893964890388833416225105 3670473667791625062168829)
    ·
      refine ⟨1376427625421859398313311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3670473667791625062168829 1376427625421859398313311)
      ·
        refine ⟨2064641438132789097469967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1376427625421859398313311 2064641438132789097469967)
        ·
          refine ⟨3096962157199183646204951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2064641438132789097469967 3096962157199183646204951)
          ·
            refine ⟨4645443235798775469307427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3096962157199183646204951 4645443235798775469307427)
            ·
              refine ⟨6968164853698163203961141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4645443235798775469307427 6968164853698163203961141)
              ·
                refine ⟨653265455034202800371357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6968164853698163203961141 653265455034202800371357)
                ·
                  refine ⟨244974545637826050139259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 653265455034202800371357 244974545637826050139259)
                  ·
                    rfl

theorem cell20_536722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_536722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536722 prefixEnd_536722 := by exact prefixLift 536722
  have htrace : WordTrace (prefixWord ++ tailWord_536722) baseStart_536722 baseEnd_536722 := by
    simpa [prefixWord, tailWord_536722, baseEnd_536722] using wordTrace_append hprefix tailTrace_536722
  have hstable : (prefixWord ++ tailWord_536722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536722).length < 2 ^ (prefixWord ++ tailWord_536722).sum := by decide
  have hdescent : baseEnd_536722 < baseStart_536722 := by decide
  rcases family_descends (prefixWord ++ tailWord_536722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536819 : List Nat := [1, 1, 1, 2, 2, 4, 2, 4, 3]
def baseStart_536819 : Nat := 118140960795 + 536819 * 2 ^ 59
def prefixEnd_536819 : Nat := 4983230072969 + 3 ^ 40 * 536819 * 2
def baseEnd_536819 : Nat := 245018819080924823905529

theorem tailTrace_536819 : CollatzResearch.WordTrace tailWord_536819 prefixEnd_536819 245018819080924823905529 := by
  unfold tailWord_536819
  simp only [CollatzResearch.WordTrace]
  refine ⟨19579397442203919231181511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13052931628135946154121007 19579397442203919231181511)
  ·
    refine ⟨29369096163305878846772267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19579397442203919231181511 29369096163305878846772267)
    ·
      refine ⟨44053644244958818270158401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29369096163305878846772267 44053644244958818270158401)
      ·
        refine ⟨33040233183719113702618801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44053644244958818270158401 33040233183719113702618801)
        ·
          refine ⟨24780174887789335276964101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33040233183719113702618801 24780174887789335276964101)
          ·
            refine ⟨4646282791460500364430769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24780174887789335276964101 4646282791460500364430769)
            ·
              refine ⟨3484712093595375273323077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4646282791460500364430769 3484712093595375273323077)
              ·
                refine ⟨653383517549132863748077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3484712093595375273323077 653383517549132863748077)
                ·
                  refine ⟨245018819080924823905529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 653383517549132863748077 245018819080924823905529)
                  ·
                    rfl

theorem cell20_536819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 3].length) (baseStart_536819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536819 prefixEnd_536819 := by exact prefixLift 536819
  have htrace : WordTrace (prefixWord ++ tailWord_536819) baseStart_536819 baseEnd_536819 := by
    simpa [prefixWord, tailWord_536819, baseEnd_536819] using wordTrace_append hprefix tailTrace_536819
  have hstable : (prefixWord ++ tailWord_536819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536819).length < 2 ^ (prefixWord ++ tailWord_536819).sum := by decide
  have hdescent : baseEnd_536819 < baseStart_536819 := by decide
  rcases family_descends (prefixWord ++ tailWord_536819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536822 : List Nat := [5, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_536822 : Nat := 118140960795 + 536822 * 2 ^ 59
def prefixEnd_536822 : Nat := 4983230072969 + 3 ^ 40 * 536822 * 2
def baseEnd_536822 : Nat := 245020188362670146805517

theorem tailTrace_536822 : CollatzResearch.WordTrace tailWord_536822 prefixEnd_536822 245020188362670146805517 := by
  unfold tailWord_536822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1223719178824565671471295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13053004574128700495693813 1223719178824565671471295)
  ·
    refine ⟨1835578768236848507206943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1223719178824565671471295 1835578768236848507206943)
    ·
      refine ⟨2753368152355272760810415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1835578768236848507206943 2753368152355272760810415)
      ·
        refine ⟨4130052228532909141215623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2753368152355272760810415 4130052228532909141215623)
        ·
          refine ⟨6195078342799363711823435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4130052228532909141215623 6195078342799363711823435)
          ·
            refine ⟨9292617514199045567735153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6195078342799363711823435 9292617514199045567735153)
            ·
              refine ⟨6969463135649284175801365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9292617514199045567735153 6969463135649284175801365)
              ·
                refine ⟨326693584483560195740689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6969463135649284175801365 326693584483560195740689)
                ·
                  refine ⟨245020188362670146805517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326693584483560195740689 245020188362670146805517)
                  ·
                    rfl

theorem cell20_536822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_536822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536822 prefixEnd_536822 := by exact prefixLift 536822
  have htrace : WordTrace (prefixWord ++ tailWord_536822) baseStart_536822 baseEnd_536822 := by
    simpa [prefixWord, tailWord_536822, baseEnd_536822] using wordTrace_append hprefix tailTrace_536822
  have hstable : (prefixWord ++ tailWord_536822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536822).length < 2 ^ (prefixWord ++ tailWord_536822).sum := by decide
  have hdescent : baseEnd_536822 < baseStart_536822 := by decide
  rcases family_descends (prefixWord ++ tailWord_536822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536895 : List Nat := [1, 1, 2, 2, 4, 1, 1, 5, 3]
def baseStart_536895 : Nat := 118140960795 + 536895 * 2 ^ 59
def prefixEnd_536895 : Nat := 4983230072969 + 3 ^ 40 * 536895 * 2
def baseEnd_536895 : Nat := 245053507551806337371885

theorem tailTrace_536895 : CollatzResearch.WordTrace tailWord_536895 prefixEnd_536895 245053507551806337371885 := by
  unfold tailWord_536895
  simp only [CollatzResearch.WordTrace]
  refine ⟨19582169389928584210948139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13054779593285722807298759 19582169389928584210948139)
  ·
    refine ⟨29373254084892876316422209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19582169389928584210948139 29373254084892876316422209)
    ·
      refine ⟨22029940563669657237316657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29373254084892876316422209 22029940563669657237316657)
      ·
        refine ⟨16522455422752242927987493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22029940563669657237316657 16522455422752242927987493)
        ·
          refine ⟨3097960391766045548997655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16522455422752242927987493 3097960391766045548997655)
          ·
            refine ⟨4646940587649068323496483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3097960391766045548997655 4646940587649068323496483)
            ·
              refine ⟨6970410881473602485244725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4646940587649068323496483 6970410881473602485244725)
              ·
                refine ⟨653476020138150232991693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6970410881473602485244725 653476020138150232991693)
                ·
                  refine ⟨245053507551806337371885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 653476020138150232991693 245053507551806337371885)
                  ·
                    rfl

theorem cell20_536895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5, 3].length) (baseStart_536895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536895 prefixEnd_536895 := by exact prefixLift 536895
  have htrace : WordTrace (prefixWord ++ tailWord_536895) baseStart_536895 baseEnd_536895 := by
    simpa [prefixWord, tailWord_536895, baseEnd_536895] using wordTrace_append hprefix tailTrace_536895
  have hstable : (prefixWord ++ tailWord_536895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536895).length < 2 ^ (prefixWord ++ tailWord_536895).sum := by decide
  have hdescent : baseEnd_536895 < baseStart_536895 := by decide
  rcases family_descends (prefixWord ++ tailWord_536895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536933 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 5]
def baseStart_536933 : Nat := 118140960795 + 536933 * 2 ^ 59
def prefixEnd_536933 : Nat := 4983230072969 + 3 ^ 40 * 536933 * 2
def baseEnd_536933 : Nat := 245070851787247094105063

theorem tailTrace_536933 : CollatzResearch.WordTrace tailWord_536933 prefixEnd_536933 245070851787247094105063 := by
  unfold tailWord_536933
  simp only [CollatzResearch.WordTrace]
  refine ⟨19583555363790916700831453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13055703575860611133887635 19583555363790916700831453)
  ·
    refine ⟨7343833261421593762811795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19583555363790916700831453 7343833261421593762811795)
    ·
      refine ⟨11015749892132390644217693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7343833261421593762811795 11015749892132390644217693)
      ·
        refine ⟨4130906209549646491581635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11015749892132390644217693 4130906209549646491581635)
        ·
          refine ⟨6196359314324469737372453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4130906209549646491581635 6196359314324469737372453)
          ·
            refine ⟨1161817371435838075757335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6196359314324469737372453 1161817371435838075757335)
            ·
              refine ⟨1742726057153757113636003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161817371435838075757335 1742726057153757113636003)
              ·
                refine ⟨2614089085730635670454005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1742726057153757113636003 2614089085730635670454005)
                ·
                  refine ⟨245070851787247094105063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2614089085730635670454005 245070851787247094105063)
                  ·
                    rfl

theorem cell20_536933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_536933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536933 prefixEnd_536933 := by exact prefixLift 536933
  have htrace : WordTrace (prefixWord ++ tailWord_536933) baseStart_536933 baseEnd_536933 := by
    simpa [prefixWord, tailWord_536933, baseEnd_536933] using wordTrace_append hprefix tailTrace_536933
  have hstable : (prefixWord ++ tailWord_536933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536933).length < 2 ^ (prefixWord ++ tailWord_536933).sum := by decide
  have hdescent : baseEnd_536933 < baseStart_536933 := by decide
  rcases family_descends (prefixWord ++ tailWord_536933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536936 : List Nat := [2, 1, 4, 2, 2, 1, 2, 4, 2]
def baseStart_536936 : Nat := 118140960795 + 536936 * 2 ^ 59
def prefixEnd_536936 : Nat := 4983230072969 + 3 ^ 40 * 536936 * 2
def baseEnd_536936 : Nat := 245072221068992417005051

theorem tailTrace_536936 : CollatzResearch.WordTrace tailWord_536936 prefixEnd_536936 245072221068992417005051 := by
  unfold tailWord_536936
  simp only [CollatzResearch.WordTrace]
  refine ⟨9791832391390024106595331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13055776521853365475460441 9791832391390024106595331)
  ·
    refine ⟨14687748587085036159892997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9791832391390024106595331 14687748587085036159892997)
    ·
      refine ⟨2753952860078444279979937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14687748587085036159892997 2753952860078444279979937)
      ·
        refine ⟨2065464645058833209984953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2753952860078444279979937 2065464645058833209984953)
        ·
          refine ⟨1549098483794124907488715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2065464645058833209984953 1549098483794124907488715)
          ·
            refine ⟨2323647725691187361233073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1549098483794124907488715 2323647725691187361233073)
            ·
              refine ⟨1742735794268390520924805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2323647725691187361233073 1742735794268390520924805)
              ·
                refine ⟨326762961425323222673401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1742735794268390520924805 326762961425323222673401)
                ·
                  refine ⟨245072221068992417005051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326762961425323222673401 245072221068992417005051)
                  ·
                    rfl

theorem cell20_536936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 2].length) (baseStart_536936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536936 prefixEnd_536936 := by exact prefixLift 536936
  have htrace : WordTrace (prefixWord ++ tailWord_536936) baseStart_536936 baseEnd_536936 := by
    simpa [prefixWord, tailWord_536936, baseEnd_536936] using wordTrace_append hprefix tailTrace_536936
  have hstable : (prefixWord ++ tailWord_536936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536936).length < 2 ^ (prefixWord ++ tailWord_536936).sum := by decide
  have hdescent : baseEnd_536936 < baseStart_536936 := by decide
  rcases family_descends (prefixWord ++ tailWord_536936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536954 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_536954 : Nat := 118140960795 + 536954 * 2 ^ 59
def prefixEnd_536954 : Nat := 4983230072969 + 3 ^ 40 * 536954 * 2
def baseEnd_536954 : Nat := 245080436759464354404977

theorem tailTrace_536954 : CollatzResearch.WordTrace tailWord_536954 prefixEnd_536954 245080436759464354404977 := by
  unfold tailWord_536954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4896080324178709321836479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13056214197809891524897277 4896080324178709321836479)
  ·
    refine ⟨7344120486268063982754719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4896080324178709321836479 7344120486268063982754719)
    ·
      refine ⟨11016180729402095974132079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7344120486268063982754719 11016180729402095974132079)
      ·
        refine ⟨16524271094103143961198119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11016180729402095974132079 16524271094103143961198119)
        ·
          refine ⟨24786406641154715941797179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16524271094103143961198119 24786406641154715941797179)
          ·
            refine ⟨37179609961732073912695769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24786406641154715941797179 37179609961732073912695769)
            ·
              refine ⟨27884707471299055434521827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37179609961732073912695769 27884707471299055434521827)
              ·
                refine ⟨41827061206948583151782741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27884707471299055434521827 41827061206948583151782741)
                ·
                  refine ⟨245080436759464354404977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41827061206948583151782741 245080436759464354404977)
                  ·
                    rfl

theorem cell20_536954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_536954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536954 prefixEnd_536954 := by exact prefixLift 536954
  have htrace : WordTrace (prefixWord ++ tailWord_536954) baseStart_536954 baseEnd_536954 := by
    simpa [prefixWord, tailWord_536954, baseEnd_536954] using wordTrace_append hprefix tailTrace_536954
  have hstable : (prefixWord ++ tailWord_536954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536954).length < 2 ^ (prefixWord ++ tailWord_536954).sum := by decide
  have hdescent : baseEnd_536954 < baseStart_536954 := by decide
  rcases family_descends (prefixWord ++ tailWord_536954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536970 : List Nat := [3, 1, 2, 5, 1, 2, 1, 3, 2]
def baseStart_536970 : Nat := 118140960795 + 536970 * 2 ^ 59
def prefixEnd_536970 : Nat := 4983230072969 + 3 ^ 40 * 536970 * 2
def baseEnd_536970 : Nat := 245087739595439409871579

theorem tailTrace_536970 : CollatzResearch.WordTrace tailWord_536970 prefixEnd_536970 245087739595439409871579 := by
  unfold tailWord_536970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4896226216164218004982091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13056603243104581346618909 4896226216164218004982091)
  ·
    refine ⟨7344339324246327007473137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4896226216164218004982091 7344339324246327007473137)
    ·
      refine ⟨5508254493184745255604853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7344339324246327007473137 5508254493184745255604853)
      ·
        refine ⟨516398858736069867712955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5508254493184745255604853 516398858736069867712955)
        ·
          refine ⟨774598288104104801569433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516398858736069867712955 774598288104104801569433)
          ·
            refine ⟨580948716078078601177075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 774598288104104801569433 580948716078078601177075)
            ·
              refine ⟨871423074117117901765613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580948716078078601177075 871423074117117901765613)
              ·
                refine ⟨326783652793919213162105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 871423074117117901765613 326783652793919213162105)
                ·
                  refine ⟨245087739595439409871579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326783652793919213162105 245087739595439409871579)
                  ·
                    rfl

theorem cell20_536970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_536970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536970 prefixEnd_536970 := by exact prefixLift 536970
  have htrace : WordTrace (prefixWord ++ tailWord_536970) baseStart_536970 baseEnd_536970 := by
    simpa [prefixWord, tailWord_536970, baseEnd_536970] using wordTrace_append hprefix tailTrace_536970
  have hstable : (prefixWord ++ tailWord_536970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536970).length < 2 ^ (prefixWord ++ tailWord_536970).sum := by decide
  have hdescent : baseEnd_536970 < baseStart_536970 := by decide
  rcases family_descends (prefixWord ++ tailWord_536970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_536995 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 4]
def baseStart_536995 : Nat := 118140960795 + 536995 * 2 ^ 59
def prefixEnd_536995 : Nat := 4983230072969 + 3 ^ 40 * 536995 * 2
def baseEnd_536995 : Nat := 245099150276650434038143

theorem tailTrace_536995 : CollatzResearch.WordTrace tailWord_536995 prefixEnd_536995 245099150276650434038143 := by
  unfold tailWord_536995
  simp only [CollatzResearch.WordTrace]
  refine ⟨19585816689566301289588439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13057211126377534193058959 19585816689566301289588439)
  ·
    refine ⟨29378725034349451934382659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19585816689566301289588439 29378725034349451934382659)
    ·
      refine ⟨44068087551524177901573989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29378725034349451934382659 44068087551524177901573989)
      ·
        refine ⟨8262766415910783356545123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44068087551524177901573989 8262766415910783356545123)
        ·
          refine ⟨12394149623866175034817685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8262766415910783356545123 12394149623866175034817685)
          ·
            refine ⟨580975763618726954757079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12394149623866175034817685 580975763618726954757079)
            ·
              refine ⟨871463645428090432135619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580975763618726954757079 871463645428090432135619)
              ·
                refine ⟨1307195468142135648203429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 871463645428090432135619 1307195468142135648203429)
                ·
                  refine ⟨245099150276650434038143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1307195468142135648203429 245099150276650434038143)
                  ·
                    rfl

theorem cell20_536995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 4].length) (baseStart_536995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_536995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_536995 prefixEnd_536995 := by exact prefixLift 536995
  have htrace : WordTrace (prefixWord ++ tailWord_536995) baseStart_536995 baseEnd_536995 := by
    simpa [prefixWord, tailWord_536995, baseEnd_536995] using wordTrace_append hprefix tailTrace_536995
  have hstable : (prefixWord ++ tailWord_536995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_536995).length < 2 ^ (prefixWord ++ tailWord_536995).sum := by decide
  have hdescent : baseEnd_536995 < baseStart_536995 := by decide
  rcases family_descends (prefixWord ++ tailWord_536995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537005 : List Nat := [1, 5, 2, 2, 2, 1, 1, 3, 3]
def baseStart_537005 : Nat := 118140960795 + 537005 * 2 ^ 59
def prefixEnd_537005 : Nat := 4983230072969 + 3 ^ 40 * 537005 * 2
def baseEnd_537005 : Nat := 245103714549134843704769

theorem tailTrace_537005 : CollatzResearch.WordTrace tailWord_537005 prefixEnd_537005 245103714549134843704769 := by
  unfold tailWord_537005
  simp only [CollatzResearch.WordTrace]
  refine ⟨19586181419530072997452469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13057454279686715331634979 19586181419530072997452469)
  ·
    refine ⟨1836204508080944343511169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19586181419530072997452469 1836204508080944343511169)
    ·
      refine ⟨1377153381060708257633377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1836204508080944343511169 1377153381060708257633377)
      ·
        refine ⟨1032865035795531193225033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1377153381060708257633377 1032865035795531193225033)
        ·
          refine ⟨774648776846648394918775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032865035795531193225033 774648776846648394918775)
          ·
            refine ⟨1161973165269972592378163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774648776846648394918775 1161973165269972592378163)
            ·
              refine ⟨1742959747904958888567245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1161973165269972592378163 1742959747904958888567245)
              ·
                refine ⟨653609905464359583212717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1742959747904958888567245 653609905464359583212717)
                ·
                  refine ⟨245103714549134843704769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 653609905464359583212717 245103714549134843704769)
                  ·
                    rfl

theorem cell20_537005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_537005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537005 prefixEnd_537005 := by exact prefixLift 537005
  have htrace : WordTrace (prefixWord ++ tailWord_537005) baseStart_537005 baseEnd_537005 := by
    simpa [prefixWord, tailWord_537005, baseEnd_537005] using wordTrace_append hprefix tailTrace_537005
  have hstable : (prefixWord ++ tailWord_537005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537005).length < 2 ^ (prefixWord ++ tailWord_537005).sum := by decide
  have hdescent : baseEnd_537005 < baseStart_537005 := by decide
  rcases family_descends (prefixWord ++ tailWord_537005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537099 : List Nat := [1, 1, 1, 1, 7, 2, 7]
def baseStart_537099 : Nat := 118140960795 + 537099 * 2 ^ 59
def prefixEnd_537099 : Nat := 4983230072969 + 3 ^ 40 * 537099 * 2
def baseEnd_537099 : Nat := 27238513190054254952339

theorem tailTrace_537099 : CollatzResearch.WordTrace tailWord_537099 prefixEnd_537099 27238513190054254952339 := by
  unfold tailWord_537099
  simp only [CollatzResearch.WordTrace]
  refine ⟨19589609881189527051374351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13059739920793018034249567 19589609881189527051374351)
  ·
    refine ⟨29384414821784290577061527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19589609881189527051374351 29384414821784290577061527)
    ·
      refine ⟨44076622232676435865592291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29384414821784290577061527 44076622232676435865592291)
      ·
        refine ⟨66114933349014653798388437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44076622232676435865592291 66114933349014653798388437)
        ·
          refine ⟨1549568750367530948399729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 66114933349014653798388437 1549568750367530948399729)
          ·
            refine ⟨1162176562775648211299797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1549568750367530948399729 1162176562775648211299797)
            ·
              refine ⟨27238513190054254952339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1162176562775648211299797 27238513190054254952339)
              ·
                rfl

theorem cell20_537099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 7].length) (baseStart_537099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537099 prefixEnd_537099 := by exact prefixLift 537099
  have htrace : WordTrace (prefixWord ++ tailWord_537099) baseStart_537099 baseEnd_537099 := by
    simpa [prefixWord, tailWord_537099, baseEnd_537099] using wordTrace_append hprefix tailTrace_537099
  have hstable : (prefixWord ++ tailWord_537099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537099).length < 2 ^ (prefixWord ++ tailWord_537099).sum := by decide
  have hdescent : baseEnd_537099 < baseStart_537099 := by decide
  rcases family_descends (prefixWord ++ tailWord_537099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537102 : List Nat := [4, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_537102 : Nat := 118140960795 + 537102 * 2 ^ 59
def prefixEnd_537102 : Nat := 4983230072969 + 3 ^ 40 * 537102 * 2
def baseEnd_537102 : Nat := 245147987992233617471039

theorem tailTrace_537102 : CollatzResearch.WordTrace tailWord_537102 prefixEnd_537102 245147987992233617471039 := by
  unfold tailWord_537102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2448714912522332320466695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13059812866785772375822373 2448714912522332320466695)
  ·
    refine ⟨3673072368783498480700043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2448714912522332320466695 3673072368783498480700043)
    ·
      refine ⟨5509608553175247721050065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3673072368783498480700043 5509608553175247721050065)
      ·
        refine ⟨4132206414881435790787549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5509608553175247721050065 4132206414881435790787549)
        ·
          refine ⟨1549577405580538421545331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4132206414881435790787549 1549577405580538421545331)
          ·
            refine ⟨2324366108370807632317997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1549577405580538421545331 2324366108370807632317997)
            ·
              refine ⟨871637290639052862119249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2324366108370807632317997 871637290639052862119249)
              ·
                refine ⟨653727967979289646589437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871637290639052862119249 653727967979289646589437)
                ·
                  refine ⟨245147987992233617471039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 653727967979289646589437 245147987992233617471039)
                  ·
                    rfl

theorem cell20_537102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_537102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537102 prefixEnd_537102 := by exact prefixLift 537102
  have htrace : WordTrace (prefixWord ++ tailWord_537102) baseStart_537102 baseEnd_537102 := by
    simpa [prefixWord, tailWord_537102, baseEnd_537102] using wordTrace_append hprefix tailTrace_537102
  have hstable : (prefixWord ++ tailWord_537102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537102).length < 2 ^ (prefixWord ++ tailWord_537102).sum := by decide
  have hdescent : baseEnd_537102 < baseStart_537102 := by decide
  rcases family_descends (prefixWord ++ tailWord_537102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537109 : List Nat := [1, 3, 2, 1, 3, 1, 1, 6, 2]
def baseStart_537109 : Nat := 118140960795 + 537109 * 2 ^ 59
def prefixEnd_537109 : Nat := 4983230072969 + 3 ^ 40 * 537109 * 2
def baseEnd_537109 : Nat := 245151182982972704237677

theorem tailTrace_537109 : CollatzResearch.WordTrace tailWord_537109 prefixEnd_537109 245151182982972704237677 := by
  unfold tailWord_537109
  simp only [CollatzResearch.WordTrace]
  refine ⟨19589974611153298759238381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13059983074102199172825587 19589974611153298759238381)
  ·
    refine ⟨7346240479182487034714393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19589974611153298759238381 7346240479182487034714393)
    ·
      refine ⟨5509680359386865276035795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7346240479182487034714393 5509680359386865276035795)
      ·
        refine ⟨8264520539080297914053693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5509680359386865276035795 8264520539080297914053693)
        ·
          refine ⟨3099195202155111717770135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8264520539080297914053693 3099195202155111717770135)
          ·
            refine ⟨4648792803232667576655203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3099195202155111717770135 4648792803232667576655203)
            ·
              refine ⟨6973189204849001364982805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4648792803232667576655203 6973189204849001364982805)
              ·
                refine ⟨326868243977296938983569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6973189204849001364982805 326868243977296938983569)
                ·
                  refine ⟨245151182982972704237677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326868243977296938983569 245151182982972704237677)
                  ·
                    rfl

theorem cell20_537109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_537109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537109 prefixEnd_537109 := by exact prefixLift 537109
  have htrace : WordTrace (prefixWord ++ tailWord_537109) baseStart_537109 baseEnd_537109 := by
    simpa [prefixWord, tailWord_537109, baseEnd_537109] using wordTrace_append hprefix tailTrace_537109
  have hstable : (prefixWord ++ tailWord_537109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537109).length < 2 ^ (prefixWord ++ tailWord_537109).sum := by decide
  have hdescent : baseEnd_537109 < baseStart_537109 := by decide
  rcases family_descends (prefixWord ++ tailWord_537109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537113 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 8]
def baseStart_537113 : Nat := 118140960795 + 537113 * 2 ^ 59
def prefixEnd_537113 : Nat := 4983230072969 + 3 ^ 40 * 537113 * 2
def baseEnd_537113 : Nat := 245153008691966468104327

theorem tailTrace_537113 : CollatzResearch.WordTrace tailWord_537113 prefixEnd_537113 245153008691966468104327 := by
  unfold tailWord_537113
  simp only [CollatzResearch.WordTrace]
  refine ⟨19590120503138807442383993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13060080335425871628255995 19590120503138807442383993)
  ·
    refine ⟨14692590377354105581787995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19590120503138807442383993 14692590377354105581787995)
    ·
      refine ⟨22038885566031158372681993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14692590377354105581787995 22038885566031158372681993)
      ·
        refine ⟨16529164174523368779511495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22038885566031158372681993 16529164174523368779511495)
        ·
          refine ⟨24793746261785053169267243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16529164174523368779511495 24793746261785053169267243)
          ·
            refine ⟨37190619392677579753900865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24793746261785053169267243 37190619392677579753900865)
            ·
              refine ⟨27892964544508184815425649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37190619392677579753900865 27892964544508184815425649)
              ·
                refine ⟨20919723408381138611569237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27892964544508184815425649 20919723408381138611569237)
                ·
                  refine ⟨245153008691966468104327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20919723408381138611569237 245153008691966468104327)
                  ·
                    rfl

theorem cell20_537113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_537113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537113 prefixEnd_537113 := by exact prefixLift 537113
  have htrace : WordTrace (prefixWord ++ tailWord_537113) baseStart_537113 baseEnd_537113 := by
    simpa [prefixWord, tailWord_537113, baseEnd_537113] using wordTrace_append hprefix tailTrace_537113
  have hstable : (prefixWord ++ tailWord_537113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537113).length < 2 ^ (prefixWord ++ tailWord_537113).sum := by decide
  have hdescent : baseEnd_537113 < baseStart_537113 := by decide
  rcases family_descends (prefixWord ++ tailWord_537113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537144 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_537144 : Nat := 118140960795 + 537144 * 2 ^ 59
def prefixEnd_537144 : Nat := 4983230072969 + 3 ^ 40 * 537144 * 2
def baseEnd_537144 : Nat := 245167157936668138070867

theorem tailTrace_537144 : CollatzResearch.WordTrace tailWord_537144 prefixEnd_537144 245167157936668138070867 := by
  unfold tailWord_537144
  simp only [CollatzResearch.WordTrace]
  refine ⟨9795625583013249868381243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13060834110684333157841657 9795625583013249868381243)
  ·
    refine ⟨14693438374519874802571865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9795625583013249868381243 14693438374519874802571865)
    ·
      refine ⟨11020078780889906101928899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14693438374519874802571865 11020078780889906101928899)
      ·
        refine ⟨16530118171334859152893349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11020078780889906101928899 16530118171334859152893349)
        ·
          refine ⟨3099397157125286091167503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16530118171334859152893349 3099397157125286091167503)
          ·
            refine ⟨4649095735687929136751255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3099397157125286091167503 4649095735687929136751255)
            ·
              refine ⟨6973643603531893705126883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4649095735687929136751255 6973643603531893705126883)
              ·
                refine ⟨10460465405297840557690325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6973643603531893705126883 10460465405297840557690325)
                ·
                  refine ⟨245167157936668138070867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10460465405297840557690325 245167157936668138070867)
                  ·
                    rfl

theorem cell20_537144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_537144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537144 prefixEnd_537144 := by exact prefixLift 537144
  have htrace : WordTrace (prefixWord ++ tailWord_537144) baseStart_537144 baseEnd_537144 := by
    simpa [prefixWord, tailWord_537144, baseEnd_537144] using wordTrace_append hprefix tailTrace_537144
  have hstable : (prefixWord ++ tailWord_537144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537144).length < 2 ^ (prefixWord ++ tailWord_537144).sum := by decide
  have hdescent : baseEnd_537144 < baseStart_537144 := by decide
  rcases family_descends (prefixWord ++ tailWord_537144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537150 : List Nat := [4, 2, 1, 4, 2, 1, 6]
def baseStart_537150 : Nat := 118140960795 + 537150 * 2 ^ 59
def prefixEnd_537150 : Nat := 4983230072969 + 3 ^ 40 * 537150 * 2
def baseEnd_537150 : Nat := 27241099611128753763427

theorem tailTrace_537150 : CollatzResearch.WordTrace tailWord_537150 prefixEnd_537150 27241099611128753763427 := by
  unfold tailWord_537150
  simp only [CollatzResearch.WordTrace]
  refine ⟨2448933750500595345185113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13060980002669841840987269 2448933750500595345185113)
  ·
    refine ⟨1836700312875446508888835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2448933750500595345185113 1836700312875446508888835)
    ·
      refine ⟨2755050469313169763333253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1836700312875446508888835 2755050469313169763333253)
      ·
        refine ⟨516571962996219330624985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2755050469313169763333253 516571962996219330624985)
        ·
          refine ⟨387428972247164497968739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516571962996219330624985 387428972247164497968739)
          ·
            refine ⟨581143458370746746953109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387428972247164497968739 581143458370746746953109)
            ·
              refine ⟨27241099611128753763427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 581143458370746746953109 27241099611128753763427)
              ·
                rfl

theorem cell20_537150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 6].length) (baseStart_537150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537150 prefixEnd_537150 := by exact prefixLift 537150
  have htrace : WordTrace (prefixWord ++ tailWord_537150) baseStart_537150 baseEnd_537150 := by
    simpa [prefixWord, tailWord_537150, baseEnd_537150] using wordTrace_append hprefix tailTrace_537150
  have hstable : (prefixWord ++ tailWord_537150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537150).length < 2 ^ (prefixWord ++ tailWord_537150).sum := by decide
  have hdescent : baseEnd_537150 < baseStart_537150 := by decide
  rcases family_descends (prefixWord ++ tailWord_537150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537164 : List Nat := [2, 2, 1, 3, 1, 2, 5, 2, 2]
def baseStart_537164 : Nat := 118140960795 + 537164 * 2 ^ 59
def prefixEnd_537164 : Nat := 4983230072969 + 3 ^ 40 * 537164 * 2
def baseEnd_537164 : Nat := 245176286481636957404119

theorem tailTrace_537164 : CollatzResearch.WordTrace tailWord_537164 prefixEnd_537164 245176286481636957404119 := by
  unfold tailWord_537164
  simp only [CollatzResearch.WordTrace]
  refine ⟨9795990312977021576245273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13061320417302695434993697 9795990312977021576245273)
  ·
    refine ⟨7346992734732766182183955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9795990312977021576245273 7346992734732766182183955)
    ·
      refine ⟨11020489102099149273275933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7346992734732766182183955 11020489102099149273275933)
      ·
        refine ⟨4132683413287180977478475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11020489102099149273275933 4132683413287180977478475)
        ·
          refine ⟨6199025119930771466217713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4132683413287180977478475 6199025119930771466217713)
          ·
            refine ⟨4649268839948078599663285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6199025119930771466217713 4649268839948078599663285)
            ·
              refine ⟨435868953745132368718433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4649268839948078599663285 435868953745132368718433)
              ·
                refine ⟨326901715308849276538825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435868953745132368718433 326901715308849276538825)
                ·
                  refine ⟨245176286481636957404119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326901715308849276538825 245176286481636957404119)
                  ·
                    rfl

theorem cell20_537164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_537164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537164 prefixEnd_537164 := by exact prefixLift 537164
  have htrace : WordTrace (prefixWord ++ tailWord_537164) baseStart_537164 baseEnd_537164 := by
    simpa [prefixWord, tailWord_537164, baseEnd_537164] using wordTrace_append hprefix tailTrace_537164
  have hstable : (prefixWord ++ tailWord_537164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537164).length < 2 ^ (prefixWord ++ tailWord_537164).sum := by decide
  have hdescent : baseEnd_537164 < baseStart_537164 := by decide
  rcases family_descends (prefixWord ++ tailWord_537164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537175 : List Nat := [1, 1, 3, 2, 2, 2, 4, 5]
def baseStart_537175 : Nat := 118140960795 + 537175 * 2 ^ 59
def prefixEnd_537175 : Nat := 4983230072969 + 3 ^ 40 * 537175 * 2
def baseEnd_537175 : Nat := 81727102393789936012469

theorem tailTrace_537175 : CollatzResearch.WordTrace tailWord_537175 prefixEnd_537175 81727102393789936012469 := by
  unfold tailWord_537175
  simp only [CollatzResearch.WordTrace]
  refine ⟨19592381828914192031140979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13061587885942794687427319 19592381828914192031140979)
  ·
    refine ⟨29388572743371288046711469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19592381828914192031140979 29388572743371288046711469)
    ·
      refine ⟨11020714778764233017516801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29388572743371288046711469 11020714778764233017516801)
      ·
        refine ⟨8265536084073174763137601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11020714778764233017516801 8265536084073174763137601)
        ·
          refine ⟨6199152063054881072353201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8265536084073174763137601 6199152063054881072353201)
          ·
            refine ⟨4649364047291160804264901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6199152063054881072353201 4649364047291160804264901)
            ·
              refine ⟨871755758867092650799669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4649364047291160804264901 871755758867092650799669)
              ·
                refine ⟨81727102393789936012469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 871755758867092650799669 81727102393789936012469)
                ·
                  rfl

theorem cell20_537175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 5].length) (baseStart_537175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537175 prefixEnd_537175 := by exact prefixLift 537175
  have htrace : WordTrace (prefixWord ++ tailWord_537175) baseStart_537175 baseEnd_537175 := by
    simpa [prefixWord, tailWord_537175, baseEnd_537175] using wordTrace_append hprefix tailTrace_537175
  have hstable : (prefixWord ++ tailWord_537175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537175).length < 2 ^ (prefixWord ++ tailWord_537175).sum := by decide
  have hdescent : baseEnd_537175 < baseStart_537175 := by decide
  rcases family_descends (prefixWord ++ tailWord_537175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537213 : List Nat := [1, 4, 1, 1, 5, 8]
def baseStart_537213 : Nat := 118140960795 + 537213 * 2 ^ 59
def prefixEnd_537213 : Nat := 4983230072969 + 3 ^ 40 * 537213 * 2
def baseEnd_537213 : Nat := 9081431533955946843355

theorem tailTrace_537213 : CollatzResearch.WordTrace tailWord_537213 prefixEnd_537213 9081431533955946843355 := by
  unfold tailWord_537213
  simp only [CollatzResearch.WordTrace]
  refine ⟨19593767802776524521024293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13062511868517683014016195 19593767802776524521024293)
  ·
    refine ⟨3673831463020598347692055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19593767802776524521024293 3673831463020598347692055)
    ·
      refine ⟨5510747194530897521538083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3673831463020598347692055 5510747194530897521538083)
      ·
        refine ⟨8266120791796346282307125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5510747194530897521538083 8266120791796346282307125)
        ·
          refine ⟨774948824230907463966293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8266120791796346282307125 774948824230907463966293)
          ·
            refine ⟨9081431533955946843355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 774948824230907463966293 9081431533955946843355)
            ·
              rfl

theorem cell20_537213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 8].length) (baseStart_537213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537213 prefixEnd_537213 := by exact prefixLift 537213
  have htrace : WordTrace (prefixWord ++ tailWord_537213) baseStart_537213 baseEnd_537213 := by
    simpa [prefixWord, tailWord_537213, baseEnd_537213] using wordTrace_append hprefix tailTrace_537213
  have hstable : (prefixWord ++ tailWord_537213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537213).length < 2 ^ (prefixWord ++ tailWord_537213).sum := by decide
  have hdescent : baseEnd_537213 < baseStart_537213 := by decide
  rcases family_descends (prefixWord ++ tailWord_537213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537223 : List Nat := [1, 1, 4, 2, 1, 2, 3, 4, 2]
def baseStart_537223 : Nat := 118140960795 + 537223 * 2 ^ 59
def prefixEnd_537223 : Nat := 4983230072969 + 3 ^ 40 * 537223 * 2
def baseEnd_537223 : Nat := 245203215689294974437211

theorem tailTrace_537223 : CollatzResearch.WordTrace tailWord_537223 prefixEnd_537223 245203215689294974437211 := by
  unfold tailWord_537223
  simp only [CollatzResearch.WordTrace]
  refine ⟨19594132532740296228888323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13062755021826864152592215 19594132532740296228888323)
  ·
    refine ⟨29391198799110444343332485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19594132532740296228888323 29391198799110444343332485)
    ·
      refine ⟨5510849774833208314374841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29391198799110444343332485 5510849774833208314374841)
      ·
        refine ⟨4133137331124906235781131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5510849774833208314374841 4133137331124906235781131)
        ·
          refine ⟨6199705996687359353671697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4133137331124906235781131 6199705996687359353671697)
          ·
            refine ⟨4649779497515519515253773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6199705996687359353671697 4649779497515519515253773)
            ·
              refine ⟨1743667311568319818220165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4649779497515519515253773 1743667311568319818220165)
              ·
                refine ⟨326937620919059965916281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1743667311568319818220165 326937620919059965916281)
                ·
                  refine ⟨245203215689294974437211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326937620919059965916281 245203215689294974437211)
                  ·
                    rfl

theorem cell20_537223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4, 2].length) (baseStart_537223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537223 prefixEnd_537223 := by exact prefixLift 537223
  have htrace : WordTrace (prefixWord ++ tailWord_537223) baseStart_537223 baseEnd_537223 := by
    simpa [prefixWord, tailWord_537223, baseEnd_537223] using wordTrace_append hprefix tailTrace_537223
  have hstable : (prefixWord ++ tailWord_537223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537223).length < 2 ^ (prefixWord ++ tailWord_537223).sum := by decide
  have hdescent : baseEnd_537223 < baseStart_537223 := by decide
  rcases family_descends (prefixWord ++ tailWord_537223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537244 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 6]
def baseStart_537244 : Nat := 118140960795 + 537244 * 2 ^ 59
def prefixEnd_537244 : Nat := 4983230072969 + 3 ^ 40 * 537244 * 2
def baseEnd_537244 : Nat := 245212800661512234737125

theorem tailTrace_537244 : CollatzResearch.WordTrace tailWord_537244 prefixEnd_537244 245212800661512234737125 := by
  unfold tailWord_537244
  simp only [CollatzResearch.WordTrace]
  refine ⟨9797449232832108407701393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13063265643776144543601857 9797449232832108407701393)
  ·
    refine ⟨7348086924624081305776045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9797449232832108407701393 7348086924624081305776045)
    ·
      refine ⟨2755532596734030489666017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7348086924624081305776045 2755532596734030489666017)
      ·
        refine ⟨2066649447550522867249513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2755532596734030489666017 2066649447550522867249513)
        ·
          refine ⟨1549987085662892150437135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2066649447550522867249513 1549987085662892150437135)
          ·
            refine ⟨2324980628494338225655703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1549987085662892150437135 2324980628494338225655703)
            ·
              refine ⟨3487470942741507338483555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2324980628494338225655703 3487470942741507338483555)
              ·
                refine ⟨5231206414112261007725333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3487470942741507338483555 5231206414112261007725333)
                ·
                  refine ⟨245212800661512234737125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5231206414112261007725333 245212800661512234737125)
                  ·
                    rfl

theorem cell20_537244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_537244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537244 prefixEnd_537244 := by exact prefixLift 537244
  have htrace : WordTrace (prefixWord ++ tailWord_537244) baseStart_537244 baseEnd_537244 := by
    simpa [prefixWord, tailWord_537244, baseEnd_537244] using wordTrace_append hprefix tailTrace_537244
  have hstable : (prefixWord ++ tailWord_537244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537244).length < 2 ^ (prefixWord ++ tailWord_537244).sum := by decide
  have hdescent : baseEnd_537244 < baseStart_537244 := by decide
  rcases family_descends (prefixWord ++ tailWord_537244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537271 : List Nat := [1, 1, 3, 1, 7, 1, 1, 2, 3]
def baseStart_537271 : Nat := 118140960795 + 537271 * 2 ^ 59
def prefixEnd_537271 : Nat := 4983230072969 + 3 ^ 40 * 537271 * 2
def baseEnd_537271 : Nat := 245225124197220140837015

theorem tailTrace_537271 : CollatzResearch.WordTrace tailWord_537271 prefixEnd_537271 245225124197220140837015 := by
  unfold tailWord_537271
  simp only [CollatzResearch.WordTrace]
  refine ⟨19595883236566400426635667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13063922157710933617757111 19595883236566400426635667)
  ·
    refine ⟨29393824854849600639953501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19595883236566400426635667 29393824854849600639953501)
    ·
      refine ⟨11022684320568600239982563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29393824854849600639953501 11022684320568600239982563)
      ·
        refine ⟨16534026480852900359973845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11022684320568600239982563 16534026480852900359973845)
        ·
          refine ⟨387516245644989852186887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16534026480852900359973845 387516245644989852186887)
          ·
            refine ⟨581274368467484778280331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387516245644989852186887 581274368467484778280331)
            ·
              refine ⟨871911552701227167420497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581274368467484778280331 871911552701227167420497)
              ·
                refine ⟨653933664525920375565373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871911552701227167420497 653933664525920375565373)
                ·
                  refine ⟨245225124197220140837015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 653933664525920375565373 245225124197220140837015)
                  ·
                    rfl

theorem cell20_537271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 3].length) (baseStart_537271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537271 prefixEnd_537271 := by exact prefixLift 537271
  have htrace : WordTrace (prefixWord ++ tailWord_537271) baseStart_537271 baseEnd_537271 := by
    simpa [prefixWord, tailWord_537271, baseEnd_537271] using wordTrace_append hprefix tailTrace_537271
  have hstable : (prefixWord ++ tailWord_537271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537271).length < 2 ^ (prefixWord ++ tailWord_537271).sum := by decide
  have hdescent : baseEnd_537271 < baseStart_537271 := by decide
  rcases family_descends (prefixWord ++ tailWord_537271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537316 : List Nat := [2, 3, 1, 1, 1, 6, 1, 3, 2]
def baseStart_537316 : Nat := 118140960795 + 537316 * 2 ^ 59
def prefixEnd_537316 : Nat := 4983230072969 + 3 ^ 40 * 537316 * 2
def baseEnd_537316 : Nat := 245245663423399984336831

theorem tailTrace_537316 : CollatzResearch.WordTrace tailWord_537316 prefixEnd_537316 245245663423399984336831 := by
  unfold tailWord_537316
  simp only [CollatzResearch.WordTrace]
  refine ⟨9798762260701686556011901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13065016347602248741349201 9798762260701686556011901)
  ·
    refine ⟨3674535847763132458504463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9798762260701686556011901 3674535847763132458504463)
    ·
      refine ⟨5511803771644698687756695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3674535847763132458504463 5511803771644698687756695)
      ·
        refine ⟨8267705657467048031635043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5511803771644698687756695 8267705657467048031635043)
        ·
          refine ⟨12401558486200572047452565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8267705657467048031635043 12401558486200572047452565)
          ·
            refine ⟨581323054040651814724339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12401558486200572047452565 581323054040651814724339)
            ·
              refine ⟨871984581060977722086509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581323054040651814724339 871984581060977722086509)
              ·
                refine ⟨326994217897866645782441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 871984581060977722086509 326994217897866645782441)
                ·
                  refine ⟨245245663423399984336831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 326994217897866645782441 245245663423399984336831)
                  ·
                    rfl

theorem cell20_537316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_537316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537316 prefixEnd_537316 := by exact prefixLift 537316
  have htrace : WordTrace (prefixWord ++ tailWord_537316) baseStart_537316 baseEnd_537316 := by
    simpa [prefixWord, tailWord_537316, baseEnd_537316] using wordTrace_append hprefix tailTrace_537316
  have hstable : (prefixWord ++ tailWord_537316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537316).length < 2 ^ (prefixWord ++ tailWord_537316).sum := by decide
  have hdescent : baseEnd_537316 < baseStart_537316 := by decide
  rcases family_descends (prefixWord ++ tailWord_537316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537327 : List Nat := [1, 1, 2, 1, 5, 4, 6]
def baseStart_537327 : Nat := 118140960795 + 537327 * 2 ^ 59
def prefixEnd_537327 : Nat := 4983230072969 + 3 ^ 40 * 537327 * 2
def baseEnd_537327 : Nat := 27250076013681426107791

theorem tailTrace_537327 : CollatzResearch.WordTrace tailWord_537327 prefixEnd_537327 27250076013681426107791 := by
  unfold tailWord_537327
  simp only [CollatzResearch.WordTrace]
  refine ⟨19597925724363521990674235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13065283816242347993782823 19597925724363521990674235)
  ·
    refine ⟨29396888586545282986011353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19597925724363521990674235 29396888586545282986011353)
    ·
      refine ⟨22047666439908962239508515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29396888586545282986011353 22047666439908962239508515)
      ·
        refine ⟨33071499659863443359262773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22047666439908962239508515 33071499659863443359262773)
        ·
          refine ⟨3100453093112197814930885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33071499659863443359262773 3100453093112197814930885)
          ·
            refine ⟨581334954958537090299541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3100453093112197814930885 581334954958537090299541)
            ·
              refine ⟨27250076013681426107791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 581334954958537090299541 27250076013681426107791)
              ·
                rfl

theorem cell20_537327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 6].length) (baseStart_537327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537327 prefixEnd_537327 := by exact prefixLift 537327
  have htrace : WordTrace (prefixWord ++ tailWord_537327) baseStart_537327 baseEnd_537327 := by
    simpa [prefixWord, tailWord_537327, baseEnd_537327] using wordTrace_append hprefix tailTrace_537327
  have hstable : (prefixWord ++ tailWord_537327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537327).length < 2 ^ (prefixWord ++ tailWord_537327).sum := by decide
  have hdescent : baseEnd_537327 < baseStart_537327 := by decide
  rcases family_descends (prefixWord ++ tailWord_537327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537417 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 6]
def baseStart_537417 : Nat := 118140960795 + 537417 * 2 ^ 59
def prefixEnd_537417 : Nat := 4983230072969 + 3 ^ 40 * 537417 * 2
def baseEnd_537417 : Nat := 245291762575492521969751

theorem tailTrace_537417 : CollatzResearch.WordTrace tailWord_537417 prefixEnd_537417 245291762575492521969751 := by
  unfold tailWord_537417
  simp only [CollatzResearch.WordTrace]
  refine ⟨19601208294037467361450505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13067472196024978240967003 19601208294037467361450505)
  ·
    refine ⟨14700906220528100521087879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19601208294037467361450505 14700906220528100521087879)
    ·
      refine ⟨22051359330792150781631819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14700906220528100521087879 22051359330792150781631819)
      ·
        refine ⟨33077038996188226172447729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22051359330792150781631819 33077038996188226172447729)
        ·
          refine ⟨24807779247141169629335797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33077038996188226172447729 24807779247141169629335797)
          ·
            refine ⟨2325729304419484652750231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24807779247141169629335797 2325729304419484652750231)
            ·
              refine ⟨3488593956629226979125347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2325729304419484652750231 3488593956629226979125347)
              ·
                refine ⟨5232890934943840468688021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3488593956629226979125347 5232890934943840468688021)
                ·
                  refine ⟨245291762575492521969751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5232890934943840468688021 245291762575492521969751)
                  ·
                    rfl

theorem cell20_537417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_537417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537417 prefixEnd_537417 := by exact prefixLift 537417
  have htrace : WordTrace (prefixWord ++ tailWord_537417) baseStart_537417 baseEnd_537417 := by
    simpa [prefixWord, tailWord_537417, baseEnd_537417] using wordTrace_append hprefix tailTrace_537417
  have hstable : (prefixWord ++ tailWord_537417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537417).length < 2 ^ (prefixWord ++ tailWord_537417).sum := by decide
  have hdescent : baseEnd_537417 < baseStart_537417 := by decide
  rcases family_descends (prefixWord ++ tailWord_537417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537420 : List Nat := [2, 2, 1, 3, 3, 2, 3, 4]
def baseStart_537420 : Nat := 118140960795 + 537420 * 2 ^ 59
def prefixEnd_537420 : Nat := 4983230072969 + 3 ^ 40 * 537420 * 2
def baseEnd_537420 : Nat := 81764377285745948289913

theorem tailTrace_537420 : CollatzResearch.WordTrace tailWord_537420 prefixEnd_537420 81764377285745948289913 := by
  unfold tailWord_537420
  simp only [CollatzResearch.WordTrace]
  refine ⟨9800658856513299436904857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13067545142017732582539809 9800658856513299436904857)
  ·
    refine ⟨7350494142384974577678643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9800658856513299436904857 7350494142384974577678643)
    ·
      refine ⟨11025741213577461866517965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7350494142384974577678643 11025741213577461866517965)
      ·
        refine ⟨4134652955091548199944237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11025741213577461866517965 4134652955091548199944237)
        ·
          refine ⟨1550494858159330574979089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4134652955091548199944237 1550494858159330574979089)
          ·
            refine ⟨1162871143619497931234317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1550494858159330574979089 1162871143619497931234317)
            ·
              refine ⟨436076678857311724212869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1162871143619497931234317 436076678857311724212869)
              ·
                refine ⟨81764377285745948289913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 436076678857311724212869 81764377285745948289913)
                ·
                  rfl

theorem cell20_537420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_537420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537420 prefixEnd_537420 := by exact prefixLift 537420
  have htrace : WordTrace (prefixWord ++ tailWord_537420) baseStart_537420 baseEnd_537420 := by
    simpa [prefixWord, tailWord_537420, baseEnd_537420] using wordTrace_append hprefix tailTrace_537420
  have hstable : (prefixWord ++ tailWord_537420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537420).length < 2 ^ (prefixWord ++ tailWord_537420).sum := by decide
  have hdescent : baseEnd_537420 < baseStart_537420 := by decide
  rcases family_descends (prefixWord ++ tailWord_537420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537424 : List Nat := [2, 1, 1, 1, 1, 4, 2, 8]
def baseStart_537424 : Nat := 118140960795 + 537424 * 2 ^ 59
def prefixEnd_537424 : Nat := 4983230072969 + 3 ^ 40 * 537424 * 2
def baseEnd_537424 : Nat := 81764985855410536245463

theorem tailTrace_537424 : CollatzResearch.WordTrace tailWord_537424 prefixEnd_537424 81764985855410536245463 := by
  unfold tailWord_537424
  simp only [CollatzResearch.WordTrace]
  refine ⟨9800731802506053778477663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13067642403341405037970217 9800731802506053778477663)
  ·
    refine ⟨14701097703759080667716495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9800731802506053778477663 14701097703759080667716495)
    ·
      refine ⟨22051646555638621001574743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14701097703759080667716495 22051646555638621001574743)
      ·
        refine ⟨33077469833457931502362115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22051646555638621001574743 33077469833457931502362115)
        ·
          refine ⟨49616204750186897253543173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33077469833457931502362115 49616204750186897253543173)
          ·
            refine ⟨9303038390660043235039345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49616204750186897253543173 9303038390660043235039345)
            ·
              refine ⟨6977278792995032426279509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9303038390660043235039345 6977278792995032426279509)
              ·
                refine ⟨81764985855410536245463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6977278792995032426279509 81764985855410536245463)
                ·
                  rfl

theorem cell20_537424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_537424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537424 prefixEnd_537424 := by exact prefixLift 537424
  have htrace : WordTrace (prefixWord ++ tailWord_537424) baseStart_537424 baseEnd_537424 := by
    simpa [prefixWord, tailWord_537424, baseEnd_537424] using wordTrace_append hprefix tailTrace_537424
  have hstable : (prefixWord ++ tailWord_537424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537424).length < 2 ^ (prefixWord ++ tailWord_537424).sum := by decide
  have hdescent : baseEnd_537424 < baseStart_537424 := by decide
  rcases family_descends (prefixWord ++ tailWord_537424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537444 : List Nat := [2, 3, 1, 1, 4, 3, 1, 2, 3]
def baseStart_537444 : Nat := 118140960795 + 537444 * 2 ^ 59
def prefixEnd_537444 : Nat := 4983230072969 + 3 ^ 40 * 537444 * 2
def baseEnd_537444 : Nat := 245304086111200428069641

theorem tailTrace_537444 : CollatzResearch.WordTrace tailWord_537444 prefixEnd_537444 245304086111200428069641 := by
  unfold tailWord_537444
  simp only [CollatzResearch.WordTrace]
  refine ⟨9801096532469825486341693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13068128709959767315122257 9801096532469825486341693)
  ·
    refine ⟨3675411199676184557378135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9801096532469825486341693 3675411199676184557378135)
    ·
      refine ⟨5513116799514276836067203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3675411199676184557378135 5513116799514276836067203)
      ·
        refine ⟨8269675199271415254100805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5513116799514276836067203 8269675199271415254100805)
        ·
          refine ⟨1550564099863390360143901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8269675199271415254100805 1550564099863390360143901)
          ·
            refine ⟨581461537448771385053963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1550564099863390360143901 581461537448771385053963)
            ·
              refine ⟨872192306173157077580945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581461537448771385053963 872192306173157077580945)
              ·
                refine ⟨654144229629867808185709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 872192306173157077580945 654144229629867808185709)
                ·
                  refine ⟨245304086111200428069641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 654144229629867808185709 245304086111200428069641)
                  ·
                    rfl

theorem cell20_537444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_537444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537444 prefixEnd_537444 := by exact prefixLift 537444
  have htrace : WordTrace (prefixWord ++ tailWord_537444) baseStart_537444 baseEnd_537444 := by
    simpa [prefixWord, tailWord_537444, baseEnd_537444] using wordTrace_append hprefix tailTrace_537444
  have hstable : (prefixWord ++ tailWord_537444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537444).length < 2 ^ (prefixWord ++ tailWord_537444).sum := by decide
  have hdescent : baseEnd_537444 < baseStart_537444 := by decide
  rcases family_descends (prefixWord ++ tailWord_537444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537479 : List Nat := [1, 1, 4, 2, 3, 2, 1, 6]
def baseStart_537479 : Nat := 118140960795 + 537479 * 2 ^ 59
def prefixEnd_537479 : Nat := 4983230072969 + 3 ^ 40 * 537479 * 2
def baseEnd_537479 : Nat := 81773353688298620634277

theorem tailTrace_537479 : CollatzResearch.WordTrace tailWord_537479 prefixEnd_537479 81773353688298620634277 := by
  unfold tailWord_537479
  simp only [CollatzResearch.WordTrace]
  refine ⟨19603469619812851950207491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13068979746541901300138327 19603469619812851950207491)
  ·
    refine ⟨29405204429719277925311237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19603469619812851950207491 29405204429719277925311237)
    ·
      refine ⟨5513475830572364610995857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29405204429719277925311237 5513475830572364610995857)
      ·
        refine ⟨4135106872929273458246893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5513475830572364610995857 4135106872929273458246893)
        ·
          refine ⟨1550665077348477546842585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4135106872929273458246893 1550665077348477546842585)
          ·
            refine ⟨1162998808011358160131939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1550665077348477546842585 1162998808011358160131939)
            ·
              refine ⟨1744498212017037240197909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1162998808011358160131939 1744498212017037240197909)
              ·
                refine ⟨81773353688298620634277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1744498212017037240197909 81773353688298620634277)
                ·
                  rfl

theorem cell20_537479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 6].length) (baseStart_537479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537479 prefixEnd_537479 := by exact prefixLift 537479
  have htrace : WordTrace (prefixWord ++ tailWord_537479) baseStart_537479 baseEnd_537479 := by
    simpa [prefixWord, tailWord_537479, baseEnd_537479] using wordTrace_append hprefix tailTrace_537479
  have hstable : (prefixWord ++ tailWord_537479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537479).length < 2 ^ (prefixWord ++ tailWord_537479).sum := by decide
  have hdescent : baseEnd_537479 < baseStart_537479 := by decide
  rcases family_descends (prefixWord ++ tailWord_537479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537558 : List Nat := [5, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_537558 : Nat := 118140960795 + 537558 * 2 ^ 59
def prefixEnd_537558 : Nat := 4983230072969 + 3 ^ 40 * 537558 * 2
def baseEnd_537558 : Nat := 245356118817522698269175

theorem tailTrace_537558 : CollatzResearch.WordTrace tailWord_537558 prefixEnd_537558 245356118817522698269175 := by
  unfold tailWord_537558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225396936657915527645833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13070900657684432294888885 1225396936657915527645833)
  ·
    refine ⟨919047702493436645734375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1225396936657915527645833 919047702493436645734375)
    ·
      refine ⟨1378571553740154968601563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 919047702493436645734375 1378571553740154968601563)
      ·
        refine ⟨2067857330610232452902345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1378571553740154968601563 2067857330610232452902345)
        ·
          refine ⟨1550892997957674339676759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2067857330610232452902345 1550892997957674339676759)
          ·
            refine ⟨2326339496936511509515139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1550892997957674339676759 2326339496936511509515139)
            ·
              refine ⟨3489509245404767264272709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2326339496936511509515139 3489509245404767264272709)
              ·
                refine ⟨654282983513393862051133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3489509245404767264272709 654282983513393862051133)
                ·
                  refine ⟨245356118817522698269175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 654282983513393862051133 245356118817522698269175)
                  ·
                    rfl

theorem cell20_537558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_537558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537558 prefixEnd_537558 := by exact prefixLift 537558
  have htrace : WordTrace (prefixWord ++ tailWord_537558) baseStart_537558 baseEnd_537558 := by
    simpa [prefixWord, tailWord_537558, baseEnd_537558] using wordTrace_append hprefix tailTrace_537558
  have hstable : (prefixWord ++ tailWord_537558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537558).length < 2 ^ (prefixWord ++ tailWord_537558).sum := by decide
  have hdescent : baseEnd_537558 < baseStart_537558 := by decide
  rcases family_descends (prefixWord ++ tailWord_537558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537569 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 4]
def baseStart_537569 : Nat := 118140960795 + 537569 * 2 ^ 59
def prefixEnd_537569 : Nat := 4983230072969 + 3 ^ 40 * 537569 * 2
def baseEnd_537569 : Nat := 245361139517255548902463

theorem tailTrace_537569 : CollatzResearch.WordTrace tailWord_537569 prefixEnd_537569 245361139517255548902463 := by
  unfold tailWord_537569
  simp only [CollatzResearch.WordTrace]
  refine ⟨19606752189486797320983761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13071168126324531547322507 19606752189486797320983761)
  ·
    refine ⟨14705064142115097990737821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19606752189486797320983761 14705064142115097990737821)
    ·
      refine ⟨5514399053293161746526683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14705064142115097990737821 5514399053293161746526683)
      ·
        refine ⟨8271598579939742619790025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5514399053293161746526683 8271598579939742619790025)
        ·
          refine ⟨6203698934954806964842519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8271598579939742619790025 6203698934954806964842519)
          ·
            refine ⟨9305548402432210447263779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6203698934954806964842519 9305548402432210447263779)
            ·
              refine ⟨13958322603648315670895669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9305548402432210447263779 13958322603648315670895669)
              ·
                refine ⟨1308592744092029594146469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13958322603648315670895669 1308592744092029594146469)
                ·
                  refine ⟨245361139517255548902463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1308592744092029594146469 245361139517255548902463)
                  ·
                    rfl

theorem cell20_537569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_537569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537569 prefixEnd_537569 := by exact prefixLift 537569
  have htrace : WordTrace (prefixWord ++ tailWord_537569) baseStart_537569 baseEnd_537569 := by
    simpa [prefixWord, tailWord_537569, baseEnd_537569] using wordTrace_append hprefix tailTrace_537569
  have hstable : (prefixWord ++ tailWord_537569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537569).length < 2 ^ (prefixWord ++ tailWord_537569).sum := by decide
  have hdescent : baseEnd_537569 < baseStart_537569 := by decide
  rcases family_descends (prefixWord ++ tailWord_537569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537593 : List Nat := [1, 2, 1, 3, 1, 3, 5, 4]
def baseStart_537593 : Nat := 118140960795 + 537593 * 2 ^ 59
def prefixEnd_537593 : Nat := 4983230072969 + 3 ^ 40 * 537593 * 2
def baseEnd_537593 : Nat := 81790697923739377367455

theorem tailTrace_537593 : CollatzResearch.WordTrace tailWord_537593 prefixEnd_537593 81790697923739377367455 := by
  unfold tailWord_537593
  simp only [CollatzResearch.WordTrace]
  refine ⟨19607627541399849419857433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13071751694266566279904955 19607627541399849419857433)
  ·
    refine ⟨14705720656049887064893075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19607627541399849419857433 14705720656049887064893075)
    ·
      refine ⟨22058580984074830597339613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14705720656049887064893075 22058580984074830597339613)
      ·
        refine ⟨8271967869028061474002355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22058580984074830597339613 8271967869028061474002355)
        ·
          refine ⟨12407951803542092211003533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8271967869028061474002355 12407951803542092211003533)
          ·
            refine ⟨4652981926328284579126325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12407951803542092211003533 4652981926328284579126325)
            ·
              refine ⟨436217055593276679293093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4652981926328284579126325 436217055593276679293093)
              ·
                refine ⟨81790697923739377367455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 436217055593276679293093 81790697923739377367455)
                ·
                  rfl

theorem cell20_537593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 4].length) (baseStart_537593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537593 prefixEnd_537593 := by exact prefixLift 537593
  have htrace : WordTrace (prefixWord ++ tailWord_537593) baseStart_537593 baseEnd_537593 := by
    simpa [prefixWord, tailWord_537593, baseEnd_537593] using wordTrace_append hprefix tailTrace_537593
  have hstable : (prefixWord ++ tailWord_537593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537593).length < 2 ^ (prefixWord ++ tailWord_537593).sum := by decide
  have hdescent : baseEnd_537593 < baseStart_537593 := by decide
  rcases family_descends (prefixWord ++ tailWord_537593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537607 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 6]
def baseStart_537607 : Nat := 118140960795 + 537607 * 2 ^ 59
def prefixEnd_537607 : Nat := 4983230072969 + 3 ^ 40 * 537607 * 2
def baseEnd_537607 : Nat := 245378483752696305635641

theorem tailTrace_537607 : CollatzResearch.WordTrace tailWord_537607 prefixEnd_537607 245378483752696305635641 := by
  unfold tailWord_537607
  simp only [CollatzResearch.WordTrace]
  refine ⟨19608138163349129810867075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13072092108899419873911383 19608138163349129810867075)
  ·
    refine ⟨29412207245023694716300613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19608138163349129810867075 29412207245023694716300613)
    ·
      refine ⟨5514788858441942759306365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29412207245023694716300613 5514788858441942759306365)
      ·
        refine ⟨2068045821915728534739887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5514788858441942759306365 2068045821915728534739887)
        ·
          refine ⟨3102068732873592802109831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2068045821915728534739887 3102068732873592802109831)
          ·
            refine ⟨4653103099310389203164747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3102068732873592802109831 4653103099310389203164747)
            ·
              refine ⟨6979654648965583804747121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4653103099310389203164747 6979654648965583804747121)
              ·
                refine ⟨5234740986724187853560341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6979654648965583804747121 5234740986724187853560341)
                ·
                  refine ⟨245378483752696305635641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5234740986724187853560341 245378483752696305635641)
                  ·
                    rfl

theorem cell20_537607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_537607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537607 prefixEnd_537607 := by exact prefixLift 537607
  have htrace : WordTrace (prefixWord ++ tailWord_537607) baseStart_537607 baseEnd_537607 := by
    simpa [prefixWord, tailWord_537607, baseEnd_537607] using wordTrace_append hprefix tailTrace_537607
  have hstable : (prefixWord ++ tailWord_537607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537607).length < 2 ^ (prefixWord ++ tailWord_537607).sum := by decide
  have hdescent : baseEnd_537607 < baseStart_537607 := by decide
  rcases family_descends (prefixWord ++ tailWord_537607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537624 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 4]
def baseStart_537624 : Nat := 118140960795 + 537624 * 2 ^ 59
def prefixEnd_537624 : Nat := 4983230072969 + 3 ^ 40 * 537624 * 2
def baseEnd_537624 : Nat := 245386243015919802068905

theorem tailTrace_537624 : CollatzResearch.WordTrace tailWord_537624 prefixEnd_537624 245386243015919802068905 := by
  unfold tailWord_537624
  simp only [CollatzResearch.WordTrace]
  refine ⟨9804379102143770857117963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13072505469525027809490617 9804379102143770857117963)
  ·
    refine ⟨14706568653215656285676945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9804379102143770857117963 14706568653215656285676945)
    ·
      refine ⟨11029926489911742214257709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14706568653215656285676945 11029926489911742214257709)
      ·
        refine ⟨4136222433716903330346641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11029926489911742214257709 4136222433716903330346641)
        ·
          refine ⟨3102166825287677497759981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4136222433716903330346641 3102166825287677497759981)
          ·
            refine ⟨1163312559482879061659993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3102166825287677497759981 1163312559482879061659993)
            ·
              refine ⟨872484419612159296244995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1163312559482879061659993 872484419612159296244995)
              ·
                refine ⟨1308726629418238944367493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872484419612159296244995 1308726629418238944367493)
                ·
                  refine ⟨245386243015919802068905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1308726629418238944367493 245386243015919802068905)
                  ·
                    rfl

theorem cell20_537624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_537624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537624 prefixEnd_537624 := by exact prefixLift 537624
  have htrace : WordTrace (prefixWord ++ tailWord_537624) baseStart_537624 baseEnd_537624 := by
    simpa [prefixWord, tailWord_537624, baseEnd_537624] using wordTrace_append hprefix tailTrace_537624
  have hstable : (prefixWord ++ tailWord_537624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537624).length < 2 ^ (prefixWord ++ tailWord_537624).sum := by decide
  have hdescent : baseEnd_537624 < baseStart_537624 := by decide
  rcases family_descends (prefixWord ++ tailWord_537624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537634 : List Nat := [3, 3, 1, 1, 1, 4, 3, 1, 3]
def baseStart_537634 : Nat := 118140960795 + 537634 * 2 ^ 59
def prefixEnd_537634 : Nat := 4983230072969 + 3 ^ 40 * 537634 * 2
def baseEnd_537634 : Nat := 245390807288404211735531

theorem tailTrace_537634 : CollatzResearch.WordTrace tailWord_537634 prefixEnd_537634 245390807288404211735531 := by
  unfold tailWord_537634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4902280733562828355524989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13072748622834208948066637 4902280733562828355524989)
  ·
    refine ⟨1838355275086060633321871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4902280733562828355524989 1838355275086060633321871)
    ·
      refine ⟨2757532912629090949982807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1838355275086060633321871 2757532912629090949982807)
      ·
        refine ⟨4136299368943636424974211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2757532912629090949982807 4136299368943636424974211)
        ·
          refine ⟨6204449053415454637461317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4136299368943636424974211 6204449053415454637461317)
          ·
            refine ⟨1163334197515397744523997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6204449053415454637461317 1163334197515397744523997)
            ·
              refine ⟨436250324068274154196499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1163334197515397744523997 436250324068274154196499)
              ·
                refine ⟨654375486102411231294749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436250324068274154196499 654375486102411231294749)
                ·
                  refine ⟨245390807288404211735531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 654375486102411231294749 245390807288404211735531)
                  ·
                    rfl

theorem cell20_537634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_537634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537634 prefixEnd_537634 := by exact prefixLift 537634
  have htrace : WordTrace (prefixWord ++ tailWord_537634) baseStart_537634 baseEnd_537634 := by
    simpa [prefixWord, tailWord_537634, baseEnd_537634] using wordTrace_append hprefix tailTrace_537634
  have hstable : (prefixWord ++ tailWord_537634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537634).length < 2 ^ (prefixWord ++ tailWord_537634).sum := by decide
  have hdescent : baseEnd_537634 < baseStart_537634 := by decide
  rcases family_descends (prefixWord ++ tailWord_537634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537676 : List Nat := [2, 2, 1, 3, 1, 1, 1, 6, 3]
def baseStart_537676 : Nat := 118140960795 + 537676 * 2 ^ 59
def prefixEnd_537676 : Nat := 4983230072969 + 3 ^ 40 * 537676 * 2
def baseEnd_537676 : Nat := 245409977232838732335359

theorem tailTrace_537676 : CollatzResearch.WordTrace tailWord_537676 prefixEnd_537676 245409977232838732335359 := by
  unfold tailWord_537676
  simp only [CollatzResearch.WordTrace]
  refine ⟨9805327400049577297564441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13073769866732769730085921 9805327400049577297564441)
  ·
    refine ⟨7353995550037182973173331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9805327400049577297564441 7353995550037182973173331)
    ·
      refine ⟨11030993325055774459759997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7353995550037182973173331 11030993325055774459759997)
      ·
        refine ⟨4136622496895915422409999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11030993325055774459759997 4136622496895915422409999)
        ·
          refine ⟨6204933745343873133614999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4136622496895915422409999 6204933745343873133614999)
          ·
            refine ⟨9307400618015809700422499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6204933745343873133614999 9307400618015809700422499)
            ·
              refine ⟨13961100927023714550633749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9307400618015809700422499 13961100927023714550633749)
              ·
                refine ⟨654426605954236619560957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13961100927023714550633749 654426605954236619560957)
                ·
                  refine ⟨245409977232838732335359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 654426605954236619560957 245409977232838732335359)
                  ·
                    rfl

theorem cell20_537676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_537676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537676 prefixEnd_537676 := by exact prefixLift 537676
  have htrace : WordTrace (prefixWord ++ tailWord_537676) baseStart_537676 baseEnd_537676 := by
    simpa [prefixWord, tailWord_537676, baseEnd_537676] using wordTrace_append hprefix tailTrace_537676
  have hstable : (prefixWord ++ tailWord_537676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537676).length < 2 ^ (prefixWord ++ tailWord_537676).sum := by decide
  have hdescent : baseEnd_537676 < baseStart_537676 := by decide
  rcases family_descends (prefixWord ++ tailWord_537676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537726 : List Nat := [4, 2, 4, 1, 2, 1, 2, 2, 2]
def baseStart_537726 : Nat := 118140960795 + 537726 * 2 ^ 59
def prefixEnd_537726 : Nat := 4983230072969 + 3 ^ 40 * 537726 * 2
def baseEnd_537726 : Nat := 245432798595260780668489

theorem tailTrace_537726 : CollatzResearch.WordTrace tailWord_537726 prefixEnd_537726 245432798595260780668489 := by
  unfold tailWord_537726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2451559806239751641806129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13074985633278675422966021 2451559806239751641806129)
  ·
    refine ⟨1838669854679813731354597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2451559806239751641806129 1838669854679813731354597)
    ·
      refine ⟨344750597752465074628987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1838669854679813731354597 344750597752465074628987)
      ·
        refine ⟨517125896628697611943481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344750597752465074628987 517125896628697611943481)
        ·
          refine ⟨387844422471523208957611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 517125896628697611943481 387844422471523208957611)
          ·
            refine ⟨581766633707284813436417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387844422471523208957611 581766633707284813436417)
            ·
              refine ⟨436324975280463610077313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581766633707284813436417 436324975280463610077313)
              ·
                refine ⟨327243731460347707557985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436324975280463610077313 327243731460347707557985)
                ·
                  refine ⟨245432798595260780668489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327243731460347707557985 245432798595260780668489)
                  ·
                    rfl

theorem cell20_537726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_537726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537726 prefixEnd_537726 := by exact prefixLift 537726
  have htrace : WordTrace (prefixWord ++ tailWord_537726) baseStart_537726 baseEnd_537726 := by
    simpa [prefixWord, tailWord_537726, baseEnd_537726] using wordTrace_append hprefix tailTrace_537726
  have hstable : (prefixWord ++ tailWord_537726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537726).length < 2 ^ (prefixWord ++ tailWord_537726).sum := by decide
  have hdescent : baseEnd_537726 < baseStart_537726 := by decide
  rcases family_descends (prefixWord ++ tailWord_537726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537782 : List Nat := [5, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_537782 : Nat := 118140960795 + 537782 * 2 ^ 59
def prefixEnd_537782 : Nat := 4983230072969 + 3 ^ 40 * 537782 * 2
def baseEnd_537782 : Nat := 245458358521173474801593

theorem tailTrace_537782 : CollatzResearch.WordTrace tailWord_537782 prefixEnd_537782 245458358521173474801593 := by
  unfold tailWord_537782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225907558607195918655475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13076347291810089798991733 1225907558607195918655475)
  ·
    refine ⟨1838861337910793877983213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1225907558607195918655475 1838861337910793877983213)
    ·
      refine ⟨689573001716547704243705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1838861337910793877983213 689573001716547704243705)
      ·
        refine ⟨517179751287410778182779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 689573001716547704243705 517179751287410778182779)
        ·
          refine ⟨775769626931116167274169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517179751287410778182779 775769626931116167274169)
          ·
            refine ⟨581827220198337125455627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 775769626931116167274169 581827220198337125455627)
            ·
              refine ⟨872740830297505688183441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581827220198337125455627 872740830297505688183441)
              ·
                refine ⟨654555622723129266137581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 872740830297505688183441 654555622723129266137581)
                ·
                  refine ⟨245458358521173474801593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 654555622723129266137581 245458358521173474801593)
                  ·
                    rfl

theorem cell20_537782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_537782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537782 prefixEnd_537782 := by exact prefixLift 537782
  have htrace : WordTrace (prefixWord ++ tailWord_537782) baseStart_537782 baseEnd_537782 := by
    simpa [prefixWord, tailWord_537782, baseEnd_537782] using wordTrace_append hprefix tailTrace_537782
  have hstable : (prefixWord ++ tailWord_537782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537782).length < 2 ^ (prefixWord ++ tailWord_537782).sum := by decide
  have hdescent : baseEnd_537782 < baseStart_537782 := by decide
  rcases family_descends (prefixWord ++ tailWord_537782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537793 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 4]
def baseStart_537793 : Nat := 118140960795 + 537793 * 2 ^ 59
def prefixEnd_537793 : Nat := 4983230072969 + 3 ^ 40 * 537793 * 2
def baseEnd_537793 : Nat := 245463379220906325434881

theorem tailTrace_537793 : CollatzResearch.WordTrace tailWord_537793 prefixEnd_537793 245463379220906325434881 := by
  unfold tailWord_537793
  simp only [CollatzResearch.WordTrace]
  refine ⟨19614922140675283577138033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13076614760450189051425355 19614922140675283577138033)
  ·
    refine ⟨14711191605506462682853525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19614922140675283577138033 14711191605506462682853525)
    ·
      refine ⟨689587106508115438258759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14711191605506462682853525 689587106508115438258759)
      ·
        refine ⟨1034380659762173157388139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 689587106508115438258759 1034380659762173157388139)
        ·
          refine ⟨1551570989643259736082209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034380659762173157388139 1551570989643259736082209)
          ·
            refine ⟨1163678242232444802061657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1551570989643259736082209 1163678242232444802061657)
            ·
              refine ⟨872758681674333601546243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1163678242232444802061657 872758681674333601546243)
              ·
                refine ⟨1309138022511500402319365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872758681674333601546243 1309138022511500402319365)
                ·
                  refine ⟨245463379220906325434881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1309138022511500402319365 245463379220906325434881)
                  ·
                    rfl

theorem cell20_537793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_537793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537793 prefixEnd_537793 := by exact prefixLift 537793
  have htrace : WordTrace (prefixWord ++ tailWord_537793) baseStart_537793 baseEnd_537793 := by
    simpa [prefixWord, tailWord_537793, baseEnd_537793] using wordTrace_append hprefix tailTrace_537793
  have hstable : (prefixWord ++ tailWord_537793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537793).length < 2 ^ (prefixWord ++ tailWord_537793).sum := by decide
  have hdescent : baseEnd_537793 < baseStart_537793 := by decide
  rcases family_descends (prefixWord ++ tailWord_537793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537844 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 4]
def baseStart_537844 : Nat := 118140960795 + 537844 * 2 ^ 59
def prefixEnd_537844 : Nat := 4983230072969 + 3 ^ 40 * 537844 * 2
def baseEnd_537844 : Nat := 245486657010576814734673

theorem tailTrace_537844 : CollatzResearch.WordTrace tailWord_537844 prefixEnd_537844 245486657010576814734673 := by
  unfold tailWord_537844
  simp only [CollatzResearch.WordTrace]
  refine ⟨9808391131745259643622293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13077854842327012858163057 9808391131745259643622293)
  ·
    refine ⟨459768334300559045794795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9808391131745259643622293 459768334300559045794795)
    ·
      refine ⟨689652501450838568692193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 459768334300559045794795 689652501450838568692193)
      ·
        refine ⟨517239376088128926519145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 689652501450838568692193 517239376088128926519145)
        ·
          refine ⟨387929532066096694889359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 517239376088128926519145 387929532066096694889359)
          ·
            refine ⟨581894298099145042334039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387929532066096694889359 581894298099145042334039)
            ·
              refine ⟨872841447148717563501059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581894298099145042334039 872841447148717563501059)
              ·
                refine ⟨1309262170723076345251589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872841447148717563501059 1309262170723076345251589)
                ·
                  refine ⟨245486657010576814734673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1309262170723076345251589 245486657010576814734673)
                  ·
                    rfl

theorem cell20_537844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_537844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537844 prefixEnd_537844 := by exact prefixLift 537844
  have htrace : WordTrace (prefixWord ++ tailWord_537844) baseStart_537844 baseEnd_537844 := by
    simpa [prefixWord, tailWord_537844, baseEnd_537844] using wordTrace_append hprefix tailTrace_537844
  have hstable : (prefixWord ++ tailWord_537844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537844).length < 2 ^ (prefixWord ++ tailWord_537844).sum := by decide
  have hdescent : baseEnd_537844 < baseStart_537844 := by decide
  rcases family_descends (prefixWord ++ tailWord_537844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537849 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 5]
def baseStart_537849 : Nat := 118140960795 + 537849 * 2 ^ 59
def prefixEnd_537849 : Nat := 4983230072969 + 3 ^ 40 * 537849 * 2
def baseEnd_537849 : Nat := 245488939146819019567985

theorem tailTrace_537849 : CollatzResearch.WordTrace tailWord_537849 prefixEnd_537849 245488939146819019567985 := by
  unfold tailWord_537849
  simp only [CollatzResearch.WordTrace]
  refine ⟨19616964628472405141176601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13077976418981603427451067 19616964628472405141176601)
  ·
    refine ⟨14712723471354303855882451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19616964628472405141176601 14712723471354303855882451)
    ·
      refine ⟨22069085207031455783823677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14712723471354303855882451 22069085207031455783823677)
      ·
        refine ⟨8275906952636795918933879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22069085207031455783823677 8275906952636795918933879)
        ·
          refine ⟨12413860428955193878400819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8275906952636795918933879 12413860428955193878400819)
          ·
            refine ⟨18620790643432790817601229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12413860428955193878400819 18620790643432790817601229)
            ·
              refine ⟨6982796491287296556600461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18620790643432790817601229 6982796491287296556600461)
              ·
                refine ⟨2618548684232736208725173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6982796491287296556600461 2618548684232736208725173)
                ·
                  refine ⟨245488939146819019567985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2618548684232736208725173 245488939146819019567985)
                  ·
                    rfl

theorem cell20_537849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_537849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537849 prefixEnd_537849 := by exact prefixLift 537849
  have htrace : WordTrace (prefixWord ++ tailWord_537849) baseStart_537849 baseEnd_537849 := by
    simpa [prefixWord, tailWord_537849, baseEnd_537849] using wordTrace_append hprefix tailTrace_537849
  have hstable : (prefixWord ++ tailWord_537849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537849).length < 2 ^ (prefixWord ++ tailWord_537849).sum := by decide
  have hdescent : baseEnd_537849 < baseStart_537849 := by decide
  rcases family_descends (prefixWord ++ tailWord_537849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537858 : List Nat := [3, 4, 1, 1, 4, 1, 2, 1, 3]
def baseStart_537858 : Nat := 118140960795 + 537858 * 2 ^ 59
def prefixEnd_537858 : Nat := 4983230072969 + 3 ^ 40 * 537858 * 2
def baseEnd_537858 : Nat := 245493046992054988267949

theorem tailTrace_537858 : CollatzResearch.WordTrace tailWord_537858 prefixEnd_537858 245493046992054988267949 := by
  unfold tailWord_537858
  simp only [CollatzResearch.WordTrace]
  refine ⟨4904323221359949919563557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13078195256959866452169485 4904323221359949919563557)
  ·
    refine ⟨919560604004990609918167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4904323221359949919563557 919560604004990609918167)
    ·
      refine ⟨1379340906007485914877251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 919560604004990609918167 1379340906007485914877251)
      ·
        refine ⟨2069011359011228872315877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1379340906007485914877251 2069011359011228872315877)
        ·
          refine ⟨387939629814605413559227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2069011359011228872315877 387939629814605413559227)
          ·
            refine ⟨581909444721908120338841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387939629814605413559227 581909444721908120338841)
            ·
              refine ⟨436432083541431090254131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581909444721908120338841 436432083541431090254131)
              ·
                refine ⟨654648125312146635381197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436432083541431090254131 654648125312146635381197)
                ·
                  refine ⟨245493046992054988267949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 654648125312146635381197 245493046992054988267949)
                  ·
                    rfl

theorem cell20_537858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_537858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537858 prefixEnd_537858 := by exact prefixLift 537858
  have htrace : WordTrace (prefixWord ++ tailWord_537858) baseStart_537858 baseEnd_537858 := by
    simpa [prefixWord, tailWord_537858, baseEnd_537858] using wordTrace_append hprefix tailTrace_537858
  have hstable : (prefixWord ++ tailWord_537858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537858).length < 2 ^ (prefixWord ++ tailWord_537858).sum := by decide
  have hdescent : baseEnd_537858 < baseStart_537858 := by decide
  rcases family_descends (prefixWord ++ tailWord_537858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537880 : List Nat := [2, 1, 2, 3, 1, 3, 2, 6]
def baseStart_537880 : Nat := 118140960795 + 537880 * 2 ^ 59
def prefixEnd_537880 : Nat := 4983230072969 + 3 ^ 40 * 537880 * 2
def baseEnd_537880 : Nat := 81834362797173563178175

theorem tailTrace_537880 : CollatzResearch.WordTrace tailWord_537880 prefixEnd_537880 81834362797173563178175 := by
  unfold tailWord_537880
  simp only [CollatzResearch.WordTrace]
  refine ⟨9809047645680048717777547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13078730194240064957036729 9809047645680048717777547)
  ·
    refine ⟨14713571468520073076666321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9809047645680048717777547 14713571468520073076666321)
    ·
      refine ⟨11035178601390054807499741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14713571468520073076666321 11035178601390054807499741)
      ·
        refine ⟨4138191975521270552812403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11035178601390054807499741 4138191975521270552812403)
        ·
          refine ⟨6207287963281905829218605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4138191975521270552812403 6207287963281905829218605)
          ·
            refine ⟨2327732986230714685956977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6207287963281905829218605 2327732986230714685956977)
            ·
              refine ⟨1745799739673036014467733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2327732986230714685956977 1745799739673036014467733)
              ·
                refine ⟨81834362797173563178175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1745799739673036014467733 81834362797173563178175)
                ·
                  rfl

theorem cell20_537880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_537880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537880 prefixEnd_537880 := by exact prefixLift 537880
  have htrace : WordTrace (prefixWord ++ tailWord_537880) baseStart_537880 baseEnd_537880 := by
    simpa [prefixWord, tailWord_537880, baseEnd_537880] using wordTrace_append hprefix tailTrace_537880
  have hstable : (prefixWord ++ tailWord_537880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537880).length < 2 ^ (prefixWord ++ tailWord_537880).sum := by decide
  have hdescent : baseEnd_537880 < baseStart_537880 := by decide
  rcases family_descends (prefixWord ++ tailWord_537880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537904 : List Nat := [2, 1, 1, 1, 2, 2, 6, 2, 3]
def baseStart_537904 : Nat := 118140960795 + 537904 * 2 ^ 59
def prefixEnd_537904 : Nat := 4983230072969 + 3 ^ 40 * 537904 * 2
def baseEnd_537904 : Nat := 245514042645483272734427

theorem tailTrace_537904 : CollatzResearch.WordTrace tailWord_537904 prefixEnd_537904 245514042645483272734427 := by
  unfold tailWord_537904
  simp only [CollatzResearch.WordTrace]
  refine ⟨9809485321636574767214383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13079313762182099689619177 9809485321636574767214383)
  ·
    refine ⟨14714227982454862150821575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9809485321636574767214383 14714227982454862150821575)
    ·
      refine ⟨22071341973682293226232363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14714227982454862150821575 22071341973682293226232363)
      ·
        refine ⟨33107012960523439839348545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22071341973682293226232363 33107012960523439839348545)
        ·
          refine ⟨24830259720392579879511409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33107012960523439839348545 24830259720392579879511409)
          ·
            refine ⟨18622694790294434909633557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24830259720392579879511409 18622694790294434909633557)
            ·
              refine ⟨872938818295051636389073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18622694790294434909633557 872938818295051636389073)
              ·
                refine ⟨654704113721288727291805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 872938818295051636389073 654704113721288727291805)
                ·
                  refine ⟨245514042645483272734427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 654704113721288727291805 245514042645483272734427)
                  ·
                    rfl

theorem cell20_537904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_537904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537904 prefixEnd_537904 := by exact prefixLift 537904
  have htrace : WordTrace (prefixWord ++ tailWord_537904) baseStart_537904 baseEnd_537904 := by
    simpa [prefixWord, tailWord_537904, baseEnd_537904] using wordTrace_append hprefix tailTrace_537904
  have hstable : (prefixWord ++ tailWord_537904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537904).length < 2 ^ (prefixWord ++ tailWord_537904).sum := by decide
  have hdescent : baseEnd_537904 < baseStart_537904 := by decide
  rcases family_descends (prefixWord ++ tailWord_537904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537907 : List Nat := [1, 1, 1, 2, 5, 2, 4, 2, 2]
def baseStart_537907 : Nat := 118140960795 + 537907 * 2 ^ 59
def prefixEnd_537907 : Nat := 4983230072969 + 3 ^ 40 * 537907 * 2
def baseEnd_537907 : Nat := 245515411927228595634415

theorem tailTrace_537907 : CollatzResearch.WordTrace tailWord_537907 prefixEnd_537907 245515411927228595634415 := by
  unfold tailWord_537907
  simp only [CollatzResearch.WordTrace]
  refine ⟨19619080062262281046787975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13079386708174854031191983 19619080062262281046787975)
  ·
    refine ⟨29428620093393421570181963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19619080062262281046787975 29428620093393421570181963)
    ·
      refine ⟨44142930140090132355272945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29428620093393421570181963 44142930140090132355272945)
      ·
        refine ⟨33107197605067599266454709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44142930140090132355272945 33107197605067599266454709)
        ·
          refine ⟨3103799775475087431230129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33107197605067599266454709 3103799775475087431230129)
          ·
            refine ⟨2327849831606315573422597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3103799775475087431230129 2327849831606315573422597)
            ·
              refine ⟨436471843426184170016737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2327849831606315573422597 436471843426184170016737)
              ·
                refine ⟨327353882569638127512553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436471843426184170016737 327353882569638127512553)
                ·
                  refine ⟨245515411927228595634415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327353882569638127512553 245515411927228595634415)
                  ·
                    rfl

theorem cell20_537907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 2].length) (baseStart_537907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537907 prefixEnd_537907 := by exact prefixLift 537907
  have htrace : WordTrace (prefixWord ++ tailWord_537907) baseStart_537907 baseEnd_537907 := by
    simpa [prefixWord, tailWord_537907, baseEnd_537907] using wordTrace_append hprefix tailTrace_537907
  have hstable : (prefixWord ++ tailWord_537907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537907).length < 2 ^ (prefixWord ++ tailWord_537907).sum := by decide
  have hdescent : baseEnd_537907 < baseStart_537907 := by decide
  rcases family_descends (prefixWord ++ tailWord_537907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537910 : List Nat := [5, 1, 2, 3, 2, 1, 1, 5]
def baseStart_537910 : Nat := 118140960795 + 537910 * 2 ^ 59
def prefixEnd_537910 : Nat := 4983230072969 + 3 ^ 40 * 537910 * 2
def baseEnd_537910 : Nat := 81838927069657972844801

theorem tailTrace_537910 : CollatzResearch.WordTrace tailWord_537910 prefixEnd_537910 81838927069657972844801 := by
  unfold tailWord_537910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1226199342578213284946699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13079459654167608372764789 1226199342578213284946699)
  ·
    refine ⟨1839299013867319927420049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1226199342578213284946699 1839299013867319927420049)
    ·
      refine ⟨1379474260400489945565037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1839299013867319927420049 1379474260400489945565037)
      ·
        refine ⟨517302847650183729586889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1379474260400489945565037 517302847650183729586889)
        ·
          refine ⟨387977135737637797190167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 517302847650183729586889 387977135737637797190167)
          ·
            refine ⟨581965703606456695785251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387977135737637797190167 581965703606456695785251)
            ·
              refine ⟨872948555409685043677877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581965703606456695785251 872948555409685043677877)
              ·
                refine ⟨81838927069657972844801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 872948555409685043677877 81838927069657972844801)
                ·
                  rfl

theorem cell20_537910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_537910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537910 prefixEnd_537910 := by exact prefixLift 537910
  have htrace : WordTrace (prefixWord ++ tailWord_537910) baseStart_537910 baseEnd_537910 := by
    simpa [prefixWord, tailWord_537910, baseEnd_537910] using wordTrace_append hprefix tailTrace_537910
  have hstable : (prefixWord ++ tailWord_537910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537910).length < 2 ^ (prefixWord ++ tailWord_537910).sum := by decide
  have hdescent : baseEnd_537910 < baseStart_537910 := by decide
  rcases family_descends (prefixWord ++ tailWord_537910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537921 : List Nat := [1, 2, 5, 2, 1, 1, 2, 3, 3]
def baseStart_537921 : Nat := 118140960795 + 537921 * 2 ^ 59
def prefixEnd_537921 : Nat := 4983230072969 + 3 ^ 40 * 537921 * 2
def baseEnd_537921 : Nat := 245521801908706769167691

theorem tailTrace_537921 : CollatzResearch.WordTrace tailWord_537921 prefixEnd_537921 245521801908706769167691 := by
  unfold tailWord_537921
  simp only [CollatzResearch.WordTrace]
  refine ⟨19619590684211561437797617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13079727122807707625198411 19619590684211561437797617)
  ·
    refine ⟨14714693013158671078348213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19619590684211561437797617 14714693013158671078348213)
    ·
      refine ⟨1379502469983625413595145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14714693013158671078348213 1379502469983625413595145)
      ·
        refine ⟨1034626852487719060196359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1379502469983625413595145 1034626852487719060196359)
        ·
          refine ⟨1551940278731578590294539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034626852487719060196359 1551940278731578590294539)
          ·
            refine ⟨2327910418097367885441809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1551940278731578590294539 2327910418097367885441809)
            ·
              refine ⟨1745932813573025914081357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2327910418097367885441809 1745932813573025914081357)
              ·
                refine ⟨654724805089884717780509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1745932813573025914081357 654724805089884717780509)
                ·
                  refine ⟨245521801908706769167691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 654724805089884717780509 245521801908706769167691)
                  ·
                    rfl

theorem cell20_537921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_537921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537921 prefixEnd_537921 := by exact prefixLift 537921
  have htrace : WordTrace (prefixWord ++ tailWord_537921) baseStart_537921 baseEnd_537921 := by
    simpa [prefixWord, tailWord_537921, baseEnd_537921] using wordTrace_append hprefix tailTrace_537921
  have hstable : (prefixWord ++ tailWord_537921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537921).length < 2 ^ (prefixWord ++ tailWord_537921).sum := by decide
  have hdescent : baseEnd_537921 < baseStart_537921 := by decide
  rcases family_descends (prefixWord ++ tailWord_537921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537956 : List Nat := [2, 3, 1, 1, 3, 3, 7]
def baseStart_537956 : Nat := 118140960795 + 537956 * 2 ^ 59
def prefixEnd_537956 : Nat := 4983230072969 + 3 ^ 40 * 537956 * 2
def baseEnd_537956 : Nat := 27281975206933578111209

theorem tailTrace_537956 : CollatzResearch.WordTrace tailWord_537956 prefixEnd_537956 27281975206933578111209 := by
  unfold tailWord_537956
  simp only [CollatzResearch.WordTrace]
  refine ⟨9810433619542381207660861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13080578159389841610214481 9810433619542381207660861)
  ·
    refine ⟨3678912607328392952872823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9810433619542381207660861 3678912607328392952872823)
    ·
      refine ⟨5518368910992589429309235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3678912607328392952872823 5518368910992589429309235)
      ·
        refine ⟨8277553366488884143963853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5518368910992589429309235 8277553366488884143963853)
        ·
          refine ⟨3104082512433331553986445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8277553366488884143963853 3104082512433331553986445)
          ·
            refine ⟨1164030942162499332744917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3104082512433331553986445 1164030942162499332744917)
            ·
              refine ⟨27281975206933578111209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1164030942162499332744917 27281975206933578111209)
              ·
                rfl

theorem cell20_537956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 7].length) (baseStart_537956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537956 prefixEnd_537956 := by exact prefixLift 537956
  have htrace : WordTrace (prefixWord ++ tailWord_537956) baseStart_537956 baseEnd_537956 := by
    simpa [prefixWord, tailWord_537956, baseEnd_537956] using wordTrace_append hprefix tailTrace_537956
  have hstable : (prefixWord ++ tailWord_537956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537956).length < 2 ^ (prefixWord ++ tailWord_537956).sum := by decide
  have hdescent : baseEnd_537956 < baseStart_537956 := by decide
  rcases family_descends (prefixWord ++ tailWord_537956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_537987 : List Nat := [1, 1, 1, 3, 5, 1, 2, 2, 4]
def baseStart_537987 : Nat := 118140960795 + 537987 * 2 ^ 59
def prefixEnd_537987 : Nat := 4983230072969 + 3 ^ 40 * 537987 * 2
def baseEnd_537987 : Nat := 245551926107103872967421

theorem tailTrace_537987 : CollatzResearch.WordTrace tailWord_537987 prefixEnd_537987 245551926107103872967421 := by
  unfold tailWord_537987
  simp only [CollatzResearch.WordTrace]
  refine ⟨19621997901972454709700215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13081331934648303139800143 19621997901972454709700215)
  ·
    refine ⟨29432996852958682064550323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19621997901972454709700215 29432996852958682064550323)
    ·
      refine ⟨44149495279438023096825485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29432996852958682064550323 44149495279438023096825485)
      ·
        refine ⟨16556060729789258661309557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44149495279438023096825485 16556060729789258661309557)
        ·
          refine ⟨1552130693417742999497771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16556060729789258661309557 1552130693417742999497771)
          ·
            refine ⟨2328196040126614499246657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1552130693417742999497771 2328196040126614499246657)
            ·
              refine ⟨1746147030094960874434993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2328196040126614499246657 1746147030094960874434993)
              ·
                refine ⟨1309610272571220655826245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1746147030094960874434993 1309610272571220655826245)
                ·
                  refine ⟨245551926107103872967421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1309610272571220655826245 245551926107103872967421)
                  ·
                    rfl

theorem cell20_537987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_537987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_537987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_537987 prefixEnd_537987 := by exact prefixLift 537987
  have htrace : WordTrace (prefixWord ++ tailWord_537987) baseStart_537987 baseEnd_537987 := by
    simpa [prefixWord, tailWord_537987, baseEnd_537987] using wordTrace_append hprefix tailTrace_537987
  have hstable : (prefixWord ++ tailWord_537987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_537987).length < 2 ^ (prefixWord ++ tailWord_537987).sum := by decide
  have hdescent : baseEnd_537987 < baseStart_537987 := by decide
  rcases family_descends (prefixWord ++ tailWord_537987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538018 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_538018 : Nat := 118140960795 + 538018 * 2 ^ 59
def prefixEnd_538018 : Nat := 4983230072969 + 3 ^ 40 * 538018 * 2
def baseEnd_538018 : Nat := 245566075351805542933961

theorem tailTrace_538018 : CollatzResearch.WordTrace tailWord_538018 prefixEnd_538018 245566075351805542933961 := by
  unfold tailWord_538018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4905782141215036751019677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13082085709906764669385805 4905782141215036751019677)
  ·
    refine ⟨1839668302955638781632379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4905782141215036751019677 1839668302955638781632379)
    ·
      refine ⟨2759502454433458172448569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1839668302955638781632379 2759502454433458172448569)
      ·
        refine ⟨2069626840825093629336427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2759502454433458172448569 2069626840825093629336427)
        ·
          refine ⟨3104440261237640444004641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2069626840825093629336427 3104440261237640444004641)
          ·
            refine ⟨2328330195928230333003481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3104440261237640444004641 2328330195928230333003481)
            ·
              refine ⟨1746247646946172749752611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2328330195928230333003481 1746247646946172749752611)
              ·
                refine ⟨2619371470419259124628917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1746247646946172749752611 2619371470419259124628917)
                ·
                  refine ⟨245566075351805542933961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2619371470419259124628917 245566075351805542933961)
                  ·
                    rfl

theorem cell20_538018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_538018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538018 prefixEnd_538018 := by exact prefixLift 538018
  have htrace : WordTrace (prefixWord ++ tailWord_538018) baseStart_538018 baseEnd_538018 := by
    simpa [prefixWord, tailWord_538018, baseEnd_538018] using wordTrace_append hprefix tailTrace_538018
  have hstable : (prefixWord ++ tailWord_538018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538018).length < 2 ^ (prefixWord ++ tailWord_538018).sum := by decide
  have hdescent : baseEnd_538018 < baseStart_538018 := by decide
  rcases family_descends (prefixWord ++ tailWord_538018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538084 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_538084 : Nat := 118140960795 + 538084 * 2 ^ 59
def prefixEnd_538084 : Nat := 4983230072969 + 3 ^ 40 * 538084 * 2
def baseEnd_538084 : Nat := 245596199550202646733691

theorem tailTrace_538084 : CollatzResearch.WordTrace tailWord_538084 prefixEnd_538084 245596199550202646733691 := by
  unfold tailWord_538084
  simp only [CollatzResearch.WordTrace]
  refine ⟨9812767891310520137990653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13083690521747360183987537 9812767891310520137990653)
  ·
    refine ⟨3679787959241445051746495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9812767891310520137990653 3679787959241445051746495)
    ·
      refine ⟨5519681938862167577619743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3679787959241445051746495 5519681938862167577619743)
      ·
        refine ⟨8279522908293251366429615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5519681938862167577619743 8279522908293251366429615)
        ·
          refine ⟨12419284362439877049644423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8279522908293251366429615 12419284362439877049644423)
          ·
            refine ⟨18628926543659815574466635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12419284362439877049644423 18628926543659815574466635)
            ·
              refine ⟨27943389815489723361699953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18628926543659815574466635 27943389815489723361699953)
              ·
                refine ⟨20957542361617292521274965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27943389815489723361699953 20957542361617292521274965)
                ·
                  refine ⟨245596199550202646733691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20957542361617292521274965 245596199550202646733691)
                  ·
                    rfl

theorem cell20_538084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_538084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538084 prefixEnd_538084 := by exact prefixLift 538084
  have htrace : WordTrace (prefixWord ++ tailWord_538084) baseStart_538084 baseEnd_538084 := by
    simpa [prefixWord, tailWord_538084, baseEnd_538084] using wordTrace_append hprefix tailTrace_538084
  have hstable : (prefixWord ++ tailWord_538084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538084).length < 2 ^ (prefixWord ++ tailWord_538084).sum := by decide
  have hdescent : baseEnd_538084 < baseStart_538084 := by decide
  rcases family_descends (prefixWord ++ tailWord_538084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538087 : List Nat := [1, 1, 5, 2, 1, 4, 1, 5]
def baseStart_538087 : Nat := 118140960795 + 538087 * 2 ^ 59
def prefixEnd_538087 : Nat := 4983230072969 + 3 ^ 40 * 538087 * 2
def baseEnd_538087 : Nat := 81865856277315989877893

theorem tailTrace_538087 : CollatzResearch.WordTrace tailWord_538087 prefixEnd_538087 81865856277315989877893 := by
  unfold tailWord_538087
  simp only [CollatzResearch.WordTrace]
  refine ⟨19625645201610171788340515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13083763467740114525560343 19625645201610171788340515)
  ·
    refine ⟨29438467802415257682510773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19625645201610171788340515 29438467802415257682510773)
    ·
      refine ⟨2759856356476430407735385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29438467802415257682510773 2759856356476430407735385)
      ·
        refine ⟨2069892267357322805801539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2759856356476430407735385 2069892267357322805801539)
        ·
          refine ⟨3104838401035984208702309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2069892267357322805801539 3104838401035984208702309)
          ·
            refine ⟨582157200194247039131683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3104838401035984208702309 582157200194247039131683)
            ·
              refine ⟨873235800291370558697525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582157200194247039131683 873235800291370558697525)
              ·
                refine ⟨81865856277315989877893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 873235800291370558697525 81865856277315989877893)
                ·
                  rfl

theorem cell20_538087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 5].length) (baseStart_538087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538087 prefixEnd_538087 := by exact prefixLift 538087
  have htrace : WordTrace (prefixWord ++ tailWord_538087) baseStart_538087 baseEnd_538087 := by
    simpa [prefixWord, tailWord_538087, baseEnd_538087] using wordTrace_append hprefix tailTrace_538087
  have hstable : (prefixWord ++ tailWord_538087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538087).length < 2 ^ (prefixWord ++ tailWord_538087).sum := by decide
  have hdescent : baseEnd_538087 < baseStart_538087 := by decide
  rcases family_descends (prefixWord ++ tailWord_538087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538091 : List Nat := [1, 1, 1, 1, 2, 3, 2, 9]
def baseStart_538091 : Nat := 118140960795 + 538091 * 2 ^ 59
def prefixEnd_538091 : Nat := 4983230072969 + 3 ^ 40 * 538091 * 2
def baseEnd_538091 : Nat := 81866464846980577833443

theorem tailTrace_538091 : CollatzResearch.WordTrace tailWord_538091 prefixEnd_538091 81866464846980577833443 := by
  unfold tailWord_538091
  simp only [CollatzResearch.WordTrace]
  refine ⟨19625791093595680471486127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13083860729063786980990751 19625791093595680471486127)
  ·
    refine ⟨29438686640393520707229191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19625791093595680471486127 29438686640393520707229191)
    ·
      refine ⟨44158029960590281060843787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29438686640393520707229191 44158029960590281060843787)
      ·
        refine ⟨66237044940885421591265681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44158029960590281060843787 66237044940885421591265681)
        ·
          refine ⟨49677783705664066193449261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66237044940885421591265681 49677783705664066193449261)
          ·
            refine ⟨18629168889624024822543473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49677783705664066193449261 18629168889624024822543473)
            ·
              refine ⟨13971876667218018616907605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18629168889624024822543473 13971876667218018616907605)
              ·
                refine ⟨81866464846980577833443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13971876667218018616907605 81866464846980577833443)
                ·
                  rfl

theorem cell20_538091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 9].length) (baseStart_538091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538091 prefixEnd_538091 := by exact prefixLift 538091
  have htrace : WordTrace (prefixWord ++ tailWord_538091) baseStart_538091 baseEnd_538091 := by
    simpa [prefixWord, tailWord_538091, baseEnd_538091] using wordTrace_append hprefix tailTrace_538091
  have hstable : (prefixWord ++ tailWord_538091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538091).length < 2 ^ (prefixWord ++ tailWord_538091).sum := by decide
  have hdescent : baseEnd_538091 < baseStart_538091 := by decide
  rcases family_descends (prefixWord ++ tailWord_538091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538094 : List Nat := [4, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_538094 : Nat := 118140960795 + 538094 * 2 ^ 59
def prefixEnd_538094 : Nat := 4983230072969 + 3 ^ 40 * 538094 * 2
def baseEnd_538094 : Nat := 245600763822687056400317

theorem tailTrace_538094 : CollatzResearch.WordTrace tailWord_538094 prefixEnd_538094 245600763822687056400317 := by
  unfold tailWord_538094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2453237564073101497980667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13083933675056541322563557 2453237564073101497980667)
  ·
    refine ⟨3679856346109652246971001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2453237564073101497980667 3679856346109652246971001)
    ·
      refine ⟨2759892259582239185228251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3679856346109652246971001 2759892259582239185228251)
      ·
        refine ⟨4139838389373358777842377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2759892259582239185228251 4139838389373358777842377)
        ·
          refine ⟨3104878792030019083381783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4139838389373358777842377 3104878792030019083381783)
          ·
            refine ⟨4657318188045028625072675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3104878792030019083381783 4657318188045028625072675)
            ·
              refine ⟨6985977282067542937609013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4657318188045028625072675 6985977282067542937609013)
              ·
                refine ⟨654935370193832150400845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6985977282067542937609013 654935370193832150400845)
                ·
                  refine ⟨245600763822687056400317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 654935370193832150400845 245600763822687056400317)
                  ·
                    rfl

theorem cell20_538094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_538094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538094 prefixEnd_538094 := by exact prefixLift 538094
  have htrace : WordTrace (prefixWord ++ tailWord_538094) baseStart_538094 baseEnd_538094 := by
    simpa [prefixWord, tailWord_538094, baseEnd_538094] using wordTrace_append hprefix tailTrace_538094
  have hstable : (prefixWord ++ tailWord_538094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538094).length < 2 ^ (prefixWord ++ tailWord_538094).sum := by decide
  have hdescent : baseEnd_538094 < baseStart_538094 := by decide
  rcases family_descends (prefixWord ++ tailWord_538094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538114 : List Nat := [3, 4, 1, 2, 1, 2, 2, 3, 2]
def baseStart_538114 : Nat := 118140960795 + 538114 * 2 ^ 59
def prefixEnd_538114 : Nat := 4983230072969 + 3 ^ 40 * 538114 * 2
def baseEnd_538114 : Nat := 245609892367655875733569

theorem tailTrace_538114 : CollatzResearch.WordTrace tailWord_538114 prefixEnd_538114 245609892367655875733569 := by
  unfold tailWord_538114
  simp only [CollatzResearch.WordTrace]
  refine ⟨4906657493128088849893349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13084419981674903599715597 4906657493128088849893349)
  ·
    refine ⟨919998279961516659355003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4906657493128088849893349 919998279961516659355003)
    ·
      refine ⟨1379997419942274989032505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 919998279961516659355003 1379997419942274989032505)
      ·
        refine ⟨1034998064956706241774379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1379997419942274989032505 1034998064956706241774379)
        ·
          refine ⟨1552497097435059362661569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034998064956706241774379 1552497097435059362661569)
          ·
            refine ⟨1164372823076294521996177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1552497097435059362661569 1164372823076294521996177)
            ·
              refine ⟨873279617307220891497133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1164372823076294521996177 873279617307220891497133)
              ·
                refine ⟨327479856490207834311425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 873279617307220891497133 327479856490207834311425)
                ·
                  refine ⟨245609892367655875733569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327479856490207834311425 245609892367655875733569)
                  ·
                    rfl

theorem cell20_538114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_538114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538114 prefixEnd_538114 := by exact prefixLift 538114
  have htrace : WordTrace (prefixWord ++ tailWord_538114) baseStart_538114 baseEnd_538114 := by
    simpa [prefixWord, tailWord_538114, baseEnd_538114] using wordTrace_append hprefix tailTrace_538114
  have hstable : (prefixWord ++ tailWord_538114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538114).length < 2 ^ (prefixWord ++ tailWord_538114).sum := by decide
  have hdescent : baseEnd_538114 < baseStart_538114 := by decide
  rcases family_descends (prefixWord ++ tailWord_538114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538129 : List Nat := [1, 2, 2, 1, 1, 2, 11]
def baseStart_538129 : Nat := 118140960795 + 538129 * 2 ^ 59
def prefixEnd_538129 : Nat := 4983230072969 + 3 ^ 40 * 538129 * 2
def baseEnd_538129 : Nat := 27290748752931387803723

theorem tailTrace_538129 : CollatzResearch.WordTrace tailWord_538129 prefixEnd_538129 27290748752931387803723 := by
  unfold tailWord_538129
  simp only [CollatzResearch.WordTrace]
  refine ⟨19627177067458012961369441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13084784711638675307579627 19627177067458012961369441)
  ·
    refine ⟨14720382800593509721027081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19627177067458012961369441 14720382800593509721027081)
    ·
      refine ⟨11040287100445132290770311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14720382800593509721027081 11040287100445132290770311)
      ·
        refine ⟨16560430650667698436155467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11040287100445132290770311 16560430650667698436155467)
        ·
          refine ⟨24840645976001547654233201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16560430650667698436155467 24840645976001547654233201)
          ·
            refine ⟨18630484482001160740674901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24840645976001547654233201 18630484482001160740674901)
            ·
              refine ⟨27290748752931387803723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18630484482001160740674901 27290748752931387803723)
              ·
                rfl

theorem cell20_538129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 11].length) (baseStart_538129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538129 prefixEnd_538129 := by exact prefixLift 538129
  have htrace : WordTrace (prefixWord ++ tailWord_538129) baseStart_538129 baseEnd_538129 := by
    simpa [prefixWord, tailWord_538129, baseEnd_538129] using wordTrace_append hprefix tailTrace_538129
  have hstable : (prefixWord ++ tailWord_538129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538129).length < 2 ^ (prefixWord ++ tailWord_538129).sum := by decide
  have hdescent : baseEnd_538129 < baseStart_538129 := by decide
  rcases family_descends (prefixWord ++ tailWord_538129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538163 : List Nat := [1, 1, 1, 2, 4, 5, 2, 4]
def baseStart_538163 : Nat := 118140960795 + 538163 * 2 ^ 59
def prefixEnd_538163 : Nat := 4983230072969 + 3 ^ 40 * 538163 * 2
def baseEnd_538163 : Nat := 81877419100943161033345

theorem tailTrace_538163 : CollatzResearch.WordTrace tailWord_538163 prefixEnd_538163 81877419100943161033345 := by
  unfold tailWord_538163
  simp only [CollatzResearch.WordTrace]
  refine ⟨19628417149334836768107143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13085611432889891178738095 19628417149334836768107143)
  ·
    refine ⟨29442625724002255152160715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19628417149334836768107143 29442625724002255152160715)
    ·
      refine ⟨44163938586003382728241073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29442625724002255152160715 44163938586003382728241073)
      ·
        refine ⟨33122953939502537046180805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44163938586003382728241073 33122953939502537046180805)
        ·
          refine ⟨6210553863656725696158901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33122953939502537046180805 6210553863656725696158901)
          ·
            refine ⟨582239424717818034014897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6210553863656725696158901 582239424717818034014897)
            ·
              refine ⟨436679568538363525511173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 582239424717818034014897 436679568538363525511173)
              ·
                refine ⟨81877419100943161033345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 436679568538363525511173 81877419100943161033345)
                ·
                  rfl

theorem cell20_538163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 4].length) (baseStart_538163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538163 prefixEnd_538163 := by exact prefixLift 538163
  have htrace : WordTrace (prefixWord ++ tailWord_538163) baseStart_538163 baseEnd_538163 := by
    simpa [prefixWord, tailWord_538163, baseEnd_538163] using wordTrace_append hprefix tailTrace_538163
  have hstable : (prefixWord ++ tailWord_538163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538163).length < 2 ^ (prefixWord ++ tailWord_538163).sum := by decide
  have hdescent : baseEnd_538163 < baseStart_538163 := by decide
  rcases family_descends (prefixWord ++ tailWord_538163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538191 : List Nat := [1, 1, 2, 1, 1, 2, 3, 6, 3]
def baseStart_538191 : Nat := 118140960795 + 538191 * 2 ^ 59
def prefixEnd_538191 : Nat := 4983230072969 + 3 ^ 40 * 538191 * 2
def baseEnd_538191 : Nat := 245645037265785830166587

theorem tailTrace_538191 : CollatzResearch.WordTrace tailWord_538191 prefixEnd_538191 245645037265785830166587 := by
  unfold tailWord_538191
  simp only [CollatzResearch.WordTrace]
  refine ⟨19629438393233397550126427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13086292262155598366750951 19629438393233397550126427)
  ·
    refine ⟨29444157589850096325189641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19629438393233397550126427 29444157589850096325189641)
    ·
      refine ⟨22083118192387572243892231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29444157589850096325189641 22083118192387572243892231)
      ·
        refine ⟨33124677288581358365838347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22083118192387572243892231 33124677288581358365838347)
        ·
          refine ⟨49687015932872037548757521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33124677288581358365838347 49687015932872037548757521)
          ·
            refine ⟨37265261949654028161568141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49687015932872037548757521 37265261949654028161568141)
            ·
              refine ⟨13974473231120260560588053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37265261949654028161568141 13974473231120260560588053)
              ·
                refine ⟨655053432708762213777565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13974473231120260560588053 655053432708762213777565)
                ·
                  refine ⟨245645037265785830166587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655053432708762213777565 245645037265785830166587)
                  ·
                    rfl

theorem cell20_538191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6, 3].length) (baseStart_538191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538191 prefixEnd_538191 := by exact prefixLift 538191
  have htrace : WordTrace (prefixWord ++ tailWord_538191) baseStart_538191 baseEnd_538191 := by
    simpa [prefixWord, tailWord_538191, baseEnd_538191] using wordTrace_append hprefix tailTrace_538191
  have hstable : (prefixWord ++ tailWord_538191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538191).length < 2 ^ (prefixWord ++ tailWord_538191).sum := by decide
  have hdescent : baseEnd_538191 < baseStart_538191 := by decide
  rcases family_descends (prefixWord ++ tailWord_538191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538194 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 4]
def baseStart_538194 : Nat := 118140960795 + 538194 * 2 ^ 59
def prefixEnd_538194 : Nat := 4983230072969 + 3 ^ 40 * 538194 * 2
def baseEnd_538194 : Nat := 245646406547531153066575

theorem tailTrace_538194 : CollatzResearch.WordTrace tailWord_538194 prefixEnd_538194 245646406547531153066575 := by
  unfold tailWord_538194
  simp only [CollatzResearch.WordTrace]
  refine ⟨4907386953055632265621409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13086365208148352708323757 4907386953055632265621409)
  ·
    refine ⟨3680540214791724199216057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4907386953055632265621409 3680540214791724199216057)
    ·
      refine ⟨2760405161093793149412043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3680540214791724199216057 2760405161093793149412043)
      ·
        refine ⟨4140607741640689724118065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2760405161093793149412043 4140607741640689724118065)
        ·
          refine ⟨3105455806230517293088549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4140607741640689724118065 3105455806230517293088549)
          ·
            refine ⟨582272963668221992454103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3105455806230517293088549 582272963668221992454103)
            ·
              refine ⟨873409445502332988681155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582272963668221992454103 873409445502332988681155)
              ·
                refine ⟨1310114168253499483021733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 873409445502332988681155 1310114168253499483021733)
                ·
                  refine ⟨245646406547531153066575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1310114168253499483021733 245646406547531153066575)
                  ·
                    rfl

theorem cell20_538194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_538194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538194 prefixEnd_538194 := by exact prefixLift 538194
  have htrace : WordTrace (prefixWord ++ tailWord_538194) baseStart_538194 baseEnd_538194 := by
    simpa [prefixWord, tailWord_538194, baseEnd_538194] using wordTrace_append hprefix tailTrace_538194
  have hstable : (prefixWord ++ tailWord_538194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538194).length < 2 ^ (prefixWord ++ tailWord_538194).sum := by decide
  have hdescent : baseEnd_538194 < baseStart_538194 := by decide
  rcases family_descends (prefixWord ++ tailWord_538194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538204 : List Nat := [2, 2, 4, 1, 2, 3, 2, 1, 3]
def baseStart_538204 : Nat := 118140960795 + 538204 * 2 ^ 59
def prefixEnd_538204 : Nat := 4983230072969 + 3 ^ 40 * 538204 * 2
def baseEnd_538204 : Nat := 245650970820015562733201

theorem tailTrace_538204 : CollatzResearch.WordTrace tailWord_538204 prefixEnd_538204 245650970820015562733201 := by
  unfold tailWord_538204
  simp only [CollatzResearch.WordTrace]
  refine ⟨9814956271093150385174833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13086608361457533846899777 9814956271093150385174833)
  ·
    refine ⟨7361217203319862788881125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9814956271093150385174833 7361217203319862788881125)
    ·
      refine ⟨1380228225622474272915211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7361217203319862788881125 1380228225622474272915211)
      ·
        refine ⟨2070342338433711409372817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1380228225622474272915211 2070342338433711409372817)
        ·
          refine ⟨1552756753825283557029613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2070342338433711409372817 1552756753825283557029613)
          ·
            refine ⟨582283782684481333886105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1552756753825283557029613 582283782684481333886105)
            ·
              refine ⟨436712837013361000414579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 582283782684481333886105 436712837013361000414579)
              ·
                refine ⟨655069255520041500621869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436712837013361000414579 655069255520041500621869)
                ·
                  refine ⟨245650970820015562733201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655069255520041500621869 245650970820015562733201)
                  ·
                    rfl

theorem cell20_538204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_538204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538204 prefixEnd_538204 := by exact prefixLift 538204
  have htrace : WordTrace (prefixWord ++ tailWord_538204) baseStart_538204 baseEnd_538204 := by
    simpa [prefixWord, tailWord_538204, baseEnd_538204] using wordTrace_append hprefix tailTrace_538204
  have hstable : (prefixWord ++ tailWord_538204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538204).length < 2 ^ (prefixWord ++ tailWord_538204).sum := by decide
  have hdescent : baseEnd_538204 < baseStart_538204 := by decide
  rcases family_descends (prefixWord ++ tailWord_538204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538270 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_538270 : Nat := 118140960795 + 538270 * 2 ^ 59
def prefixEnd_538270 : Nat := 4983230072969 + 3 ^ 40 * 538270 * 2
def baseEnd_538270 : Nat := 245681095018412666532931

theorem tailTrace_538270 : CollatzResearch.WordTrace tailWord_538270 prefixEnd_538270 245681095018412666532931 := by
  unfold tailWord_538270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2454039969993399255281533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13088213173298129361501509 2454039969993399255281533)
  ·
    refine ⟨920264988747524720730575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2454039969993399255281533 920264988747524720730575)
    ·
      refine ⟨1380397483121287081095863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 920264988747524720730575 1380397483121287081095863)
      ·
        refine ⟨2070596224681930621643795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1380397483121287081095863 2070596224681930621643795)
        ·
          refine ⟨3105894337022895932465693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2070596224681930621643795 3105894337022895932465693)
          ·
            refine ⟨1164710376383585974674635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3105894337022895932465693 1164710376383585974674635)
            ·
              refine ⟨1747065564575378962011953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1164710376383585974674635 1747065564575378962011953)
              ·
                refine ⟨1310299173431534221508965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1747065564575378962011953 1310299173431534221508965)
                ·
                  refine ⟨245681095018412666532931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1310299173431534221508965 245681095018412666532931)
                  ·
                    rfl

theorem cell20_538270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_538270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538270 prefixEnd_538270 := by exact prefixLift 538270
  have htrace : WordTrace (prefixWord ++ tailWord_538270) baseStart_538270 baseEnd_538270 := by
    simpa [prefixWord, tailWord_538270, baseEnd_538270] using wordTrace_append hprefix tailTrace_538270
  have hstable : (prefixWord ++ tailWord_538270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538270).length < 2 ^ (prefixWord ++ tailWord_538270).sum := by decide
  have hdescent : baseEnd_538270 < baseStart_538270 := by decide
  rcases family_descends (prefixWord ++ tailWord_538270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538308 : List Nat := [2, 3, 3, 1, 1, 1, 1, 6, 2]
def baseStart_538308 : Nat := 118140960795 + 538308 * 2 ^ 59
def prefixEnd_538308 : Nat := 4983230072969 + 3 ^ 40 * 538308 * 2
def baseEnd_538308 : Nat := 245698439253853423266109

theorem tailTrace_538308 : CollatzResearch.WordTrace tailWord_538308 prefixEnd_538308 245698439253853423266109 := by
  unfold tailWord_538308
  simp only [CollatzResearch.WordTrace]
  refine ⟨9816852866904763266067789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13089137155873017688090385 9816852866904763266067789)
  ·
    refine ⟨3681319825089286224775421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9816852866904763266067789 3681319825089286224775421)
    ·
      refine ⟨1380494934408482334290783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3681319825089286224775421 1380494934408482334290783)
      ·
        refine ⟨2070742401612723501436175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1380494934408482334290783 2070742401612723501436175)
        ·
          refine ⟨3106113602419085252154263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2070742401612723501436175 3106113602419085252154263)
          ·
            refine ⟨4659170403628627878231395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3106113602419085252154263 4659170403628627878231395)
            ·
              refine ⟨6988755605442941817347093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4659170403628627878231395 6988755605442941817347093)
              ·
                refine ⟨327597919005137897688145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6988755605442941817347093 327597919005137897688145)
                ·
                  refine ⟨245698439253853423266109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327597919005137897688145 245698439253853423266109)
                  ·
                    rfl

theorem cell20_538308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_538308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538308 prefixEnd_538308 := by exact prefixLift 538308
  have htrace : WordTrace (prefixWord ++ tailWord_538308) baseStart_538308 baseEnd_538308 := by
    simpa [prefixWord, tailWord_538308, baseEnd_538308] using wordTrace_append hprefix tailTrace_538308
  have hstable : (prefixWord ++ tailWord_538308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538308).length < 2 ^ (prefixWord ++ tailWord_538308).sum := by decide
  have hdescent : baseEnd_538308 < baseStart_538308 := by decide
  rcases family_descends (prefixWord ++ tailWord_538308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538336 : List Nat := [2, 1, 1, 3, 1, 2, 6, 4]
def baseStart_538336 : Nat := 118140960795 + 538336 * 2 ^ 59
def prefixEnd_538336 : Nat := 4983230072969 + 3 ^ 40 * 538336 * 2
def baseEnd_538336 : Nat := 81903739738936590110887

theorem tailTrace_538336 : CollatzResearch.WordTrace tailWord_538336 prefixEnd_538336 81903739738936590110887 := by
  unfold tailWord_538336
  simp only [CollatzResearch.WordTrace]
  refine ⟨9817363488854043657077431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13089817985138724876103241 9817363488854043657077431)
  ·
    refine ⟨14726045233281065485616147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9817363488854043657077431 14726045233281065485616147)
    ·
      refine ⟨22089067849921598228424221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14726045233281065485616147 22089067849921598228424221)
      ·
        refine ⟨8283400443720599335659083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22089067849921598228424221 8283400443720599335659083)
        ·
          refine ⟨12425100665580899003488625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8283400443720599335659083 12425100665580899003488625)
          ·
            refine ⟨9318825499185674252616469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12425100665580899003488625 9318825499185674252616469)
            ·
              refine ⟨436819945274328480591397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9318825499185674252616469 436819945274328480591397)
              ·
                refine ⟨81903739738936590110887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 436819945274328480591397 81903739738936590110887)
                ·
                  rfl

theorem cell20_538336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_538336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538336 prefixEnd_538336 := by exact prefixLift 538336
  have htrace : WordTrace (prefixWord ++ tailWord_538336) baseStart_538336 baseEnd_538336 := by
    simpa [prefixWord, tailWord_538336, baseEnd_538336] using wordTrace_append hprefix tailTrace_538336
  have hstable : (prefixWord ++ tailWord_538336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538336).length < 2 ^ (prefixWord ++ tailWord_538336).sum := by decide
  have hdescent : baseEnd_538336 < baseStart_538336 := by decide
  rcases family_descends (prefixWord ++ tailWord_538336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538346 : List Nat := [3, 1, 3, 1, 1, 1, 5, 3, 2]
def baseStart_538346 : Nat := 118140960795 + 538346 * 2 ^ 59
def prefixEnd_538346 : Nat := 4983230072969 + 3 ^ 40 * 538346 * 2
def baseEnd_538346 : Nat := 245715783489294179999287

theorem tailTrace_538346 : CollatzResearch.WordTrace tailWord_538346 prefixEnd_538346 245715783489294179999287 := by
  unfold tailWord_538346
  simp only [CollatzResearch.WordTrace]
  refine ⟨4908772926917964755504723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13090061138447906014679261 4908772926917964755504723)
  ·
    refine ⟨7363159390376947133257085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4908772926917964755504723 7363159390376947133257085)
    ·
      refine ⟨2761184771391355174971407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7363159390376947133257085 2761184771391355174971407)
      ·
        refine ⟨4141777157087032762457111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2761184771391355174971407 4141777157087032762457111)
        ·
          refine ⟨6212665735630549143685667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4141777157087032762457111 6212665735630549143685667)
          ·
            refine ⟨9318998603445823715528501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6212665735630549143685667 9318998603445823715528501)
            ·
              refine ⟨873656119073045973330797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9318998603445823715528501 873656119073045973330797)
              ·
                refine ⟨327621044652392239999049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 873656119073045973330797 327621044652392239999049)
                ·
                  refine ⟨245715783489294179999287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327621044652392239999049 245715783489294179999287)
                  ·
                    rfl

theorem cell20_538346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_538346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538346 prefixEnd_538346 := by exact prefixLift 538346
  have htrace : WordTrace (prefixWord ++ tailWord_538346) baseStart_538346 baseEnd_538346 := by
    simpa [prefixWord, tailWord_538346, baseEnd_538346] using wordTrace_append hprefix tailTrace_538346
  have hstable : (prefixWord ++ tailWord_538346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538346).length < 2 ^ (prefixWord ++ tailWord_538346).sum := by decide
  have hdescent : baseEnd_538346 < baseStart_538346 := by decide
  rcases family_descends (prefixWord ++ tailWord_538346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538367 : List Nat := [1, 1, 2, 2, 1, 3, 2, 6, 2]
def baseStart_538367 : Nat := 118140960795 + 538367 * 2 ^ 59
def prefixEnd_538367 : Nat := 4983230072969 + 3 ^ 40 * 538367 * 2
def baseEnd_538367 : Nat := 245725368461511440299201

theorem tailTrace_538367 : CollatzResearch.WordTrace tailWord_538367 prefixEnd_538367 245725368461511440299201 := by
  unfold tailWord_538367
  simp only [CollatzResearch.WordTrace]
  refine ⟨19635857640595779608533355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13090571760397186405688903 19635857640595779608533355)
  ·
    refine ⟨29453786460893669412800033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19635857640595779608533355 29453786460893669412800033)
    ·
      refine ⟨22090339845670252059600025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29453786460893669412800033 22090339845670252059600025)
      ·
        refine ⟨16567754884252689044700019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22090339845670252059600025 16567754884252689044700019)
        ·
          refine ⟨24851632326379033567050029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16567754884252689044700019 24851632326379033567050029)
          ·
            refine ⟨9319362122392137587643761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24851632326379033567050029 9319362122392137587643761)
            ·
              refine ⟨6989521591794103190732821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9319362122392137587643761 6989521591794103190732821)
              ·
                refine ⟨327633824615348587065601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6989521591794103190732821 327633824615348587065601)
                ·
                  refine ⟨245725368461511440299201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327633824615348587065601 245725368461511440299201)
                  ·
                    rfl

theorem cell20_538367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 2].length) (baseStart_538367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538367 prefixEnd_538367 := by exact prefixLift 538367
  have htrace : WordTrace (prefixWord ++ tailWord_538367) baseStart_538367 baseEnd_538367 := by
    simpa [prefixWord, tailWord_538367, baseEnd_538367] using wordTrace_append hprefix tailTrace_538367
  have hstable : (prefixWord ++ tailWord_538367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538367).length < 2 ^ (prefixWord ++ tailWord_538367).sum := by decide
  have hdescent : baseEnd_538367 < baseStart_538367 := by decide
  rcases family_descends (prefixWord ++ tailWord_538367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538429 : List Nat := [1, 4, 1, 4, 1, 3, 1, 5]
def baseStart_538429 : Nat := 118140960795 + 538429 * 2 ^ 59
def prefixEnd_538429 : Nat := 4983230072969 + 3 ^ 40 * 538429 * 2
def baseEnd_538429 : Nat := 81917888983638260077427

theorem tailTrace_538429 : CollatzResearch.WordTrace tailWord_538429 prefixEnd_538429 81917888983638260077427 := by
  unfold tailWord_538429
  simp only [CollatzResearch.WordTrace]
  refine ⟨19638118966371164197290341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13092079310914109464860227 19638118966371164197290341)
  ·
    refine ⟨3682147306194593286991939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19638118966371164197290341 3682147306194593286991939)
    ·
      refine ⟨5523220959291889930487909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3682147306194593286991939 5523220959291889930487909)
      ·
        refine ⟨1035603929867229361966483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5523220959291889930487909 1035603929867229361966483)
        ·
          refine ⟨1553405894800844042949725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1035603929867229361966483 1553405894800844042949725)
          ·
            refine ⟨582527210550316516106147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1553405894800844042949725 582527210550316516106147)
            ·
              refine ⟨873790815825474774159221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582527210550316516106147 873790815825474774159221)
              ·
                refine ⟨81917888983638260077427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 873790815825474774159221 81917888983638260077427)
                ·
                  rfl

theorem cell20_538429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 5].length) (baseStart_538429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538429 prefixEnd_538429 := by exact prefixLift 538429
  have htrace : WordTrace (prefixWord ++ tailWord_538429) baseStart_538429 baseEnd_538429 := by
    simpa [prefixWord, tailWord_538429, baseEnd_538429] using wordTrace_append hprefix tailTrace_538429
  have hstable : (prefixWord ++ tailWord_538429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538429).length < 2 ^ (prefixWord ++ tailWord_538429).sum := by decide
  have hdescent : baseEnd_538429 < baseStart_538429 := by decide
  rcases family_descends (prefixWord ++ tailWord_538429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538471 : List Nat := [1, 1, 5, 1, 2, 1, 9]
def baseStart_538471 : Nat := 118140960795 + 538471 * 2 ^ 59
def prefixEnd_538471 : Nat := 4983230072969 + 3 ^ 40 * 538471 * 2
def baseEnd_538471 : Nat := 27308092988372144536901

theorem tailTrace_538471 : CollatzResearch.WordTrace tailWord_538471 prefixEnd_538471 27308092988372144536901 := by
  unfold tailWord_538471
  simp only [CollatzResearch.WordTrace]
  refine ⟨19639650832219005370319267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13093100554812670246879511 19639650832219005370319267)
  ·
    refine ⟨29459476248328508055478901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19639650832219005370319267 29459476248328508055478901)
    ·
      refine ⟨2761825898280797630201147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29459476248328508055478901 2761825898280797630201147)
      ·
        refine ⟨4142738847421196445301721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2761825898280797630201147 4142738847421196445301721)
        ·
          refine ⟨3107054135565897333976291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4142738847421196445301721 3107054135565897333976291)
          ·
            refine ⟨4660581203348846000964437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3107054135565897333976291 4660581203348846000964437)
            ·
              refine ⟨27308092988372144536901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4660581203348846000964437 27308092988372144536901)
              ·
                rfl

theorem cell20_538471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 9].length) (baseStart_538471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538471 prefixEnd_538471 := by exact prefixLift 538471
  have htrace : WordTrace (prefixWord ++ tailWord_538471) baseStart_538471 baseEnd_538471 := by
    simpa [prefixWord, tailWord_538471, baseEnd_538471] using wordTrace_append hprefix tailTrace_538471
  have hstable : (prefixWord ++ tailWord_538471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538471).length < 2 ^ (prefixWord ++ tailWord_538471).sum := by decide
  have hdescent : baseEnd_538471 < baseStart_538471 := by decide
  rcases family_descends (prefixWord ++ tailWord_538471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538481 : List Nat := [1, 2, 2, 2, 1, 3, 1, 6, 2]
def baseStart_538481 : Nat := 118140960795 + 538481 * 2 ^ 59
def prefixEnd_538481 : Nat := 4983230072969 + 3 ^ 40 * 538481 * 2
def baseEnd_538481 : Nat := 245777401167833710498735

theorem tailTrace_538481 : CollatzResearch.WordTrace tailWord_538481 prefixEnd_538481 245777401167833710498735 := by
  unfold tailWord_538481
  simp only [CollatzResearch.WordTrace]
  refine ⟨19640015562182777078183297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13093343708121851385455531 19640015562182777078183297)
  ·
    refine ⟨14730011671637082808637473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19640015562182777078183297 14730011671637082808637473)
    ·
      refine ⟨11047508753727812106478105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14730011671637082808637473 11047508753727812106478105)
      ·
        refine ⟨8285631565295859079858579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11047508753727812106478105 8285631565295859079858579)
        ·
          refine ⟨12428447347943788619787869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8285631565295859079858579 12428447347943788619787869)
          ·
            refine ⟨4660667755478920732420451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12428447347943788619787869 4660667755478920732420451)
            ·
              refine ⟨6991001633218381098630677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4660667755478920732420451 6991001633218381098630677)
              ·
                refine ⟨327703201557111613998313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6991001633218381098630677 327703201557111613998313)
                ·
                  refine ⟨245777401167833710498735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327703201557111613998313 245777401167833710498735)
                  ·
                    rfl

theorem cell20_538481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 2].length) (baseStart_538481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538481 prefixEnd_538481 := by exact prefixLift 538481
  have htrace : WordTrace (prefixWord ++ tailWord_538481) baseStart_538481 baseEnd_538481 := by
    simpa [prefixWord, tailWord_538481, baseEnd_538481] using wordTrace_append hprefix tailTrace_538481
  have hstable : (prefixWord ++ tailWord_538481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538481).length < 2 ^ (prefixWord ++ tailWord_538481).sum := by decide
  have hdescent : baseEnd_538481 < baseStart_538481 := by decide
  rcases family_descends (prefixWord ++ tailWord_538481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538542 : List Nat := [4, 1, 5, 1, 1, 2, 2, 1, 3]
def baseStart_538542 : Nat := 118140960795 + 538542 * 2 ^ 59
def prefixEnd_538542 : Nat := 4983230072969 + 3 ^ 40 * 538542 * 2
def baseEnd_538542 : Nat := 245805243229988609465153

theorem tailTrace_538542 : CollatzResearch.WordTrace tailWord_538542 prefixEnd_538542 245805243229988609465153 := by
  unfold tailWord_538542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2455280051870223062019235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13094826943307856330769253 2455280051870223062019235)
  ·
    refine ⟨3682920077805334593028853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2455280051870223062019235 3682920077805334593028853)
    ·
      refine ⟨345273757294250118096455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3682920077805334593028853 345273757294250118096455)
      ·
        refine ⟨517910635941375177144683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345273757294250118096455 517910635941375177144683)
        ·
          refine ⟨776865953912062765717025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 517910635941375177144683 776865953912062765717025)
          ·
            refine ⟨582649465434047074287769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 776865953912062765717025 582649465434047074287769)
            ·
              refine ⟨436987099075535305715827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 582649465434047074287769 436987099075535305715827)
              ·
                refine ⟨655480648613302958573741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436987099075535305715827 655480648613302958573741)
                ·
                  refine ⟨245805243229988609465153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655480648613302958573741 245805243229988609465153)
                  ·
                    rfl

theorem cell20_538542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_538542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538542 prefixEnd_538542 := by exact prefixLift 538542
  have htrace : WordTrace (prefixWord ++ tailWord_538542) baseStart_538542 baseEnd_538542 := by
    simpa [prefixWord, tailWord_538542, baseEnd_538542] using wordTrace_append hprefix tailTrace_538542
  have hstable : (prefixWord ++ tailWord_538542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538542).length < 2 ^ (prefixWord ++ tailWord_538542).sum := by decide
  have hdescent : baseEnd_538542 < baseStart_538542 := by decide
  rcases family_descends (prefixWord ++ tailWord_538542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538547 : List Nat := [1, 1, 1, 2, 3, 1, 6, 5]
def baseStart_538547 : Nat := 118140960795 + 538547 * 2 ^ 59
def prefixEnd_538547 : Nat := 4983230072969 + 3 ^ 40 * 538547 * 2
def baseEnd_538547 : Nat := 81935841788743604766155

theorem tailTrace_538547 : CollatzResearch.WordTrace tailWord_538547 prefixEnd_538547 81935841788743604766155 := by
  unfold tailWord_538547
  simp only [CollatzResearch.WordTrace]
  refine ⟨19642422779943670350085895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13094948519962446900057263 19642422779943670350085895)
  ·
    refine ⟨29463634169915505525128843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19642422779943670350085895 29463634169915505525128843)
    ·
      refine ⟨44195451254873258287693265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29463634169915505525128843 44195451254873258287693265)
      ·
        refine ⟨33146588441154943715769949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44195451254873258287693265 33146588441154943715769949)
        ·
          refine ⟨12429970665433103893413731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33146588441154943715769949 12429970665433103893413731)
          ·
            refine ⟨18644955998149655840120597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12429970665433103893413731 18644955998149655840120597)
            ·
              refine ⟨873982312413265117505653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18644955998149655840120597 873982312413265117505653)
              ·
                refine ⟨81935841788743604766155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 873982312413265117505653 81935841788743604766155)
                ·
                  rfl

theorem cell20_538547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 5].length) (baseStart_538547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538547 prefixEnd_538547 := by exact prefixLift 538547
  have htrace : WordTrace (prefixWord ++ tailWord_538547) baseStart_538547 baseEnd_538547 := by
    simpa [prefixWord, tailWord_538547, baseEnd_538547] using wordTrace_append hprefix tailTrace_538547
  have hstable : (prefixWord ++ tailWord_538547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538547).length < 2 ^ (prefixWord ++ tailWord_538547).sum := by decide
  have hdescent : baseEnd_538547 < baseStart_538547 := by decide
  rcases family_descends (prefixWord ++ tailWord_538547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538554 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_538554 : Nat := 118140960795 + 538554 * 2 ^ 59
def prefixEnd_538554 : Nat := 4983230072969 + 3 ^ 40 * 538554 * 2
def baseEnd_538554 : Nat := 245810720356969901065103

theorem tailTrace_538554 : CollatzResearch.WordTrace tailWord_538554 prefixEnd_538554 245810720356969901065103 := by
  unfold tailWord_538554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4910669522729577636397679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13095118727278873697060477 4910669522729577636397679)
  ·
    refine ⟨7366004284094366454596519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4910669522729577636397679 7366004284094366454596519)
    ·
      refine ⟨11049006426141549681894779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7366004284094366454596519 11049006426141549681894779)
      ·
        refine ⟨16573509639212324522842169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11049006426141549681894779 16573509639212324522842169)
        ·
          refine ⟨12430132229409243392131627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16573509639212324522842169 12430132229409243392131627)
          ·
            refine ⟨18645198344113865088197441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12430132229409243392131627 18645198344113865088197441)
            ·
              refine ⟨13983898758085398816148081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18645198344113865088197441 13983898758085398816148081)
              ·
                refine ⟨10487924068564049112111061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13983898758085398816148081 10487924068564049112111061)
                ·
                  refine ⟨245810720356969901065103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10487924068564049112111061 245810720356969901065103)
                  ·
                    rfl

theorem cell20_538554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_538554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538554 prefixEnd_538554 := by exact prefixLift 538554
  have htrace : WordTrace (prefixWord ++ tailWord_538554) baseStart_538554 baseEnd_538554 := by
    simpa [prefixWord, tailWord_538554, baseEnd_538554] using wordTrace_append hprefix tailTrace_538554
  have hstable : (prefixWord ++ tailWord_538554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538554).length < 2 ^ (prefixWord ++ tailWord_538554).sum := by decide
  have hdescent : baseEnd_538554 < baseStart_538554 := by decide
  rcases family_descends (prefixWord ++ tailWord_538554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538585 : List Nat := [1, 2, 1, 2, 6, 8]
def baseStart_538585 : Nat := 118140960795 + 538585 * 2 ^ 59
def prefixEnd_538585 : Nat := 4983230072969 + 3 ^ 40 * 538585 * 2
def baseEnd_538585 : Nat := 9104624800061910038209

theorem tailTrace_538585 : CollatzResearch.WordTrace tailWord_538585 prefixEnd_538585 9104624800061910038209 := by
  unfold tailWord_538585
  simp only [CollatzResearch.WordTrace]
  refine ⟨19643808753806002839969209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13095872502537335226646139 19643808753806002839969209)
  ·
    refine ⟨14732856565354502129976907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19643808753806002839969209 14732856565354502129976907)
    ·
      refine ⟨22099284848031753194965361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14732856565354502129976907 22099284848031753194965361)
      ·
        refine ⟨16574463636023814896224021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22099284848031753194965361 16574463636023814896224021)
        ·
          refine ⟨776927982938616323260501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16574463636023814896224021 776927982938616323260501)
          ·
            refine ⟨9104624800061910038209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 776927982938616323260501 9104624800061910038209)
            ·
              rfl

theorem cell20_538585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 8].length) (baseStart_538585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538585 prefixEnd_538585 := by exact prefixLift 538585
  have htrace : WordTrace (prefixWord ++ tailWord_538585) baseStart_538585 baseEnd_538585 := by
    simpa [prefixWord, tailWord_538585, baseEnd_538585] using wordTrace_append hprefix tailTrace_538585
  have hstable : (prefixWord ++ tailWord_538585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538585).length < 2 ^ (prefixWord ++ tailWord_538585).sum := by decide
  have hdescent : baseEnd_538585 < baseStart_538585 := by decide
  rcases family_descends (prefixWord ++ tailWord_538585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538591 : List Nat := [1, 1, 2, 3, 4, 3, 2, 2, 2]
def baseStart_538591 : Nat := 118140960795 + 538591 * 2 ^ 59
def prefixEnd_538591 : Nat := 4983230072969 + 3 ^ 40 * 538591 * 2
def baseEnd_538591 : Nat := 245827608165162216831619

theorem tailTrace_538591 : CollatzResearch.WordTrace tailWord_538591 prefixEnd_538591 245827608165162216831619 := by
  unfold tailWord_538591
  simp only [CollatzResearch.WordTrace]
  refine ⟨19644027591784265864687627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13096018394522843909791751 19644027591784265864687627)
  ·
    refine ⟨29466041387676398797031441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19644027591784265864687627 29466041387676398797031441)
    ·
      refine ⟨22099531040757299097773581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29466041387676398797031441 22099531040757299097773581)
      ·
        refine ⟨8287324140283987161665093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22099531040757299097773581 8287324140283987161665093)
        ·
          refine ⟨1553873276303247592812205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8287324140283987161665093 1553873276303247592812205)
          ·
            refine ⟨582702478613717847304577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1553873276303247592812205 582702478613717847304577)
            ·
              refine ⟨437026858960288385478433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 582702478613717847304577 437026858960288385478433)
              ·
                refine ⟨327770144220216289108825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437026858960288385478433 327770144220216289108825)
                ·
                  refine ⟨245827608165162216831619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327770144220216289108825 245827608165162216831619)
                  ·
                    rfl

theorem cell20_538591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 2].length) (baseStart_538591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538591 prefixEnd_538591 := by exact prefixLift 538591
  have htrace : WordTrace (prefixWord ++ tailWord_538591) baseStart_538591 baseEnd_538591 := by
    simpa [prefixWord, tailWord_538591, baseEnd_538591] using wordTrace_append hprefix tailTrace_538591
  have hstable : (prefixWord ++ tailWord_538591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538591).length < 2 ^ (prefixWord ++ tailWord_538591).sum := by decide
  have hdescent : baseEnd_538591 < baseStart_538591 := by decide
  rcases family_descends (prefixWord ++ tailWord_538591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538592 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_538592 : Nat := 118140960795 + 538592 * 2 ^ 59
def prefixEnd_538592 : Nat := 4983230072969 + 3 ^ 40 * 538592 * 2
def baseEnd_538592 : Nat := 245828064592410657798281

theorem tailTrace_538592 : CollatzResearch.WordTrace tailWord_538592 prefixEnd_538592 245828064592410657798281 := by
  unfold tailWord_538592
  simp only [CollatzResearch.WordTrace]
  refine ⟨9822032032390321517737015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13096042709853762023649353 9822032032390321517737015)
  ·
    refine ⟨14733048048585482276605523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9822032032390321517737015 14733048048585482276605523)
    ·
      refine ⟨22099572072878223414908285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14733048048585482276605523 22099572072878223414908285)
      ·
        refine ⟨8287339527329333780590607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22099572072878223414908285 8287339527329333780590607)
        ·
          refine ⟨12431009290994000670885911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8287339527329333780590607 12431009290994000670885911)
          ·
            refine ⟨18646513936491001006328867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12431009290994000670885911 18646513936491001006328867)
            ·
              refine ⟨27969770904736501509493301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18646513936491001006328867 27969770904736501509493301)
              ·
                refine ⟨2622166022319047016514997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27969770904736501509493301 2622166022319047016514997)
                ·
                  refine ⟨245828064592410657798281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2622166022319047016514997 245828064592410657798281)
                  ·
                    rfl

theorem cell20_538592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_538592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538592 prefixEnd_538592 := by exact prefixLift 538592
  have htrace : WordTrace (prefixWord ++ tailWord_538592) baseStart_538592 baseEnd_538592 := by
    simpa [prefixWord, tailWord_538592, baseEnd_538592] using wordTrace_append hprefix tailTrace_538592
  have hstable : (prefixWord ++ tailWord_538592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538592).length < 2 ^ (prefixWord ++ tailWord_538592).sum := by decide
  have hdescent : baseEnd_538592 < baseStart_538592 := by decide
  rcases family_descends (prefixWord ++ tailWord_538592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538678 : List Nat := [5, 1, 2, 1, 1, 1, 3, 6]
def baseStart_538678 : Nat := 118140960795 + 538678 * 2 ^ 59
def prefixEnd_538678 : Nat := 4983230072969 + 3 ^ 40 * 538678 * 2
def baseEnd_538678 : Nat := 81955772445258860310421

theorem tailTrace_538678 : CollatzResearch.WordTrace tailWord_538678 prefixEnd_538678 81955772445258860310421 := by
  unfold tailWord_538678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1227950046404317482694043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13098133828312719815403125 1227950046404317482694043)
  ·
    refine ⟨1841925069606476224041065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1227950046404317482694043 1841925069606476224041065)
    ·
      refine ⟨1381443802204857168030799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1841925069606476224041065 1381443802204857168030799)
      ·
        refine ⟨2072165703307285752046199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1381443802204857168030799 2072165703307285752046199)
        ·
          refine ⟨3108248554960928628069299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2072165703307285752046199 3108248554960928628069299)
          ·
            refine ⟨4662372832441392942103949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3108248554960928628069299 4662372832441392942103949)
            ·
              refine ⟨1748389812165522353288981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4662372832441392942103949 1748389812165522353288981)
              ·
                refine ⟨81955772445258860310421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1748389812165522353288981 81955772445258860310421)
                ·
                  rfl

theorem cell20_538678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_538678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538678 prefixEnd_538678 := by exact prefixLift 538678
  have htrace : WordTrace (prefixWord ++ tailWord_538678) baseStart_538678 baseEnd_538678 := by
    simpa [prefixWord, tailWord_538678, baseEnd_538678] using wordTrace_append hprefix tailTrace_538678
  have hstable : (prefixWord ++ tailWord_538678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538678).length < 2 ^ (prefixWord ++ tailWord_538678).sum := by decide
  have hdescent : baseEnd_538678 < baseStart_538678 := by decide
  rcases family_descends (prefixWord ++ tailWord_538678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538688 : List Nat := [2, 1, 1, 2, 2, 6, 1, 3, 2]
def baseStart_538688 : Nat := 118140960795 + 538688 * 2 ^ 59
def prefixEnd_538688 : Nat := 4983230072969 + 3 ^ 40 * 538688 * 2
def baseEnd_538688 : Nat := 245871881608260990597889

theorem tailTrace_538688 : CollatzResearch.WordTrace tailWord_538688 prefixEnd_538688 245871881608260990597889 := by
  unfold tailWord_538688
  simp only [CollatzResearch.WordTrace]
  refine ⟨9823782736216425715484359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13098376981621900953979145 9823782736216425715484359)
  ·
    refine ⟨14735674104324638573226539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9823782736216425715484359 14735674104324638573226539)
    ·
      refine ⟨22103511156486957859839809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14735674104324638573226539 22103511156486957859839809)
      ·
        refine ⟨16577633367365218394879857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22103511156486957859839809 16577633367365218394879857)
        ·
          refine ⟨12433225025523913796159893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16577633367365218394879857 12433225025523913796159893)
          ·
            refine ⟨582807423071433459194995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12433225025523913796159893 582807423071433459194995)
            ·
              refine ⟨874211134607150188792493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582807423071433459194995 874211134607150188792493)
              ·
                refine ⟨327829175477681320797185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 874211134607150188792493 327829175477681320797185)
                ·
                  refine ⟨245871881608260990597889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327829175477681320797185 245871881608260990597889)
                  ·
                    rfl

theorem cell20_538688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 2].length) (baseStart_538688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538688 prefixEnd_538688 := by exact prefixLift 538688
  have htrace : WordTrace (prefixWord ++ tailWord_538688) baseStart_538688 baseEnd_538688 := by
    simpa [prefixWord, tailWord_538688, baseEnd_538688] using wordTrace_append hprefix tailTrace_538688
  have hstable : (prefixWord ++ tailWord_538688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538688).length < 2 ^ (prefixWord ++ tailWord_538688).sum := by decide
  have hdescent : baseEnd_538688 < baseStart_538688 := by decide
  rcases family_descends (prefixWord ++ tailWord_538688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538709 : List Nat := [1, 3, 2, 2, 1, 5, 1, 1, 4]
def baseStart_538709 : Nat := 118140960795 + 538709 * 2 ^ 59
def prefixEnd_538709 : Nat := 4983230072969 + 3 ^ 40 * 538709 * 2
def baseEnd_538709 : Nat := 245881466580478250897803

theorem tailTrace_538709 : CollatzResearch.WordTrace tailWord_538709 prefixEnd_538709 245881466580478250897803 := by
  unfold tailWord_538709
  simp only [CollatzResearch.WordTrace]
  refine ⟨19648331405356772017483181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13098887603571181344988787 19648331405356772017483181)
  ·
    refine ⟨7368124277008789506556193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19648331405356772017483181 7368124277008789506556193)
    ·
      refine ⟨5526093207756592129917145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7368124277008789506556193 5526093207756592129917145)
      ·
        refine ⟨4144569905817444097437859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5526093207756592129917145 4144569905817444097437859)
        ·
          refine ⟨6216854858726166146156789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4144569905817444097437859 6216854858726166146156789)
          ·
            refine ⟨582830143005578076202199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6216854858726166146156789 582830143005578076202199)
            ·
              refine ⟨874245214508367114303299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582830143005578076202199 874245214508367114303299)
              ·
                refine ⟨1311367821762550671454949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 874245214508367114303299 1311367821762550671454949)
                ·
                  refine ⟨245881466580478250897803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1311367821762550671454949 245881466580478250897803)
                  ·
                    rfl

theorem cell20_538709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_538709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538709 prefixEnd_538709 := by exact prefixLift 538709
  have htrace : WordTrace (prefixWord ++ tailWord_538709) baseStart_538709 baseEnd_538709 := by
    simpa [prefixWord, tailWord_538709, baseEnd_538709] using wordTrace_append hprefix tailTrace_538709
  have hstable : (prefixWord ++ tailWord_538709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538709).length < 2 ^ (prefixWord ++ tailWord_538709).sum := by decide
  have hdescent : baseEnd_538709 < baseStart_538709 := by decide
  rcases family_descends (prefixWord ++ tailWord_538709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538716 : List Nat := [2, 2, 4, 1, 1, 3, 2, 5]
def baseStart_538716 : Nat := 118140960795 + 538716 * 2 ^ 59
def prefixEnd_538716 : Nat := 4983230072969 + 3 ^ 40 * 538716 * 2
def baseEnd_538716 : Nat := 81961553857072445888147

theorem tailTrace_538716 : CollatzResearch.WordTrace tailWord_538716 prefixEnd_538716 81961553857072445888147 := by
  unfold tailWord_538716
  simp only [CollatzResearch.WordTrace]
  refine ⟨9824293358165706106494001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13099057810887608141992001 9824293358165706106494001)
  ·
    refine ⟨7368220018624279579870501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9824293358165706106494001 7368220018624279579870501)
    ·
      refine ⟨1381541253492052421225719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7368220018624279579870501 1381541253492052421225719)
      ·
        refine ⟨2072311880238078631838579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1381541253492052421225719 2072311880238078631838579)
        ·
          refine ⟨3108467820357117947757869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2072311880238078631838579 3108467820357117947757869)
          ·
            refine ⟨1165675432633919230409201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3108467820357117947757869 1165675432633919230409201)
            ·
              refine ⟨874256574475439422806901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1165675432633919230409201 874256574475439422806901)
              ·
                refine ⟨81961553857072445888147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 874256574475439422806901 81961553857072445888147)
                ·
                  rfl

theorem cell20_538716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_538716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538716 prefixEnd_538716 := by exact prefixLift 538716
  have htrace : WordTrace (prefixWord ++ tailWord_538716) baseStart_538716 baseEnd_538716 := by
    simpa [prefixWord, tailWord_538716, baseEnd_538716] using wordTrace_append hprefix tailTrace_538716
  have hstable : (prefixWord ++ tailWord_538716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538716).length < 2 ^ (prefixWord ++ tailWord_538716).sum := by decide
  have hdescent : baseEnd_538716 < baseStart_538716 := by decide
  rcases family_descends (prefixWord ++ tailWord_538716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538761 : List Nat := [1, 2, 1, 1, 4, 2, 4, 2, 3]
def baseStart_538761 : Nat := 118140960795 + 538761 * 2 ^ 59
def prefixEnd_538761 : Nat := 4983230072969 + 3 ^ 40 * 538761 * 2
def baseEnd_538761 : Nat := 245905200797397181164257

theorem tailTrace_538761 : CollatzResearch.WordTrace tailWord_538761 prefixEnd_538761 245905200797397181164257 := by
  unfold tailWord_538761
  simp only [CollatzResearch.WordTrace]
  refine ⟨19650228001168384898376137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13100152000778923265584091 19650228001168384898376137)
  ·
    refine ⟨14737671000876288673782103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19650228001168384898376137 14737671000876288673782103)
    ·
      refine ⟨22106506501314433010673155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14737671000876288673782103 22106506501314433010673155)
      ·
        refine ⟨33159759751971649516009733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22106506501314433010673155 33159759751971649516009733)
        ·
          refine ⟨6217454953494684284251825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33159759751971649516009733 6217454953494684284251825)
          ·
            refine ⟨4663091215121013213188869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6217454953494684284251825 4663091215121013213188869)
            ·
              refine ⟨874329602835189977472913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4663091215121013213188869 874329602835189977472913)
              ·
                refine ⟨655747202126392483104685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874329602835189977472913 655747202126392483104685)
                ·
                  refine ⟨245905200797397181164257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655747202126392483104685 245905200797397181164257)
                  ·
                    rfl

theorem cell20_538761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_538761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538761 prefixEnd_538761 := by exact prefixLift 538761
  have htrace : WordTrace (prefixWord ++ tailWord_538761) baseStart_538761 baseEnd_538761 := by
    simpa [prefixWord, tailWord_538761, baseEnd_538761] using wordTrace_append hprefix tailTrace_538761
  have hstable : (prefixWord ++ tailWord_538761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538761).length < 2 ^ (prefixWord ++ tailWord_538761).sum := by decide
  have hdescent : baseEnd_538761 < baseStart_538761 := by decide
  rcases family_descends (prefixWord ++ tailWord_538761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538798 : List Nat := [4, 1, 4, 2, 1, 1, 2, 3, 2]
def baseStart_538798 : Nat := 118140960795 + 538798 * 2 ^ 59
def prefixEnd_538798 : Nat := 4983230072969 + 3 ^ 40 * 538798 * 2
def baseEnd_538798 : Nat := 245922088605589496930773

theorem tailTrace_538798 : CollatzResearch.WordTrace tailWord_538798 prefixEnd_538798 245922088605589496930773 := by
  unfold tailWord_538798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2456447187754292527184131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13101051668022893478315365 2456447187754292527184131)
  ·
    refine ⟨3684670781631438790776197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2456447187754292527184131 3684670781631438790776197)
    ·
      refine ⟨690875771555894773270537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3684670781631438790776197 690875771555894773270537)
      ·
        refine ⟨518156828666921079952903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 690875771555894773270537 518156828666921079952903)
        ·
          refine ⟨777235243000381619929355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518156828666921079952903 777235243000381619929355)
          ·
            refine ⟨1165852864500572429894033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777235243000381619929355 1165852864500572429894033)
            ·
              refine ⟨874389648375429322420525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1165852864500572429894033 874389648375429322420525)
              ·
                refine ⟨327896118140785995907697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 874389648375429322420525 327896118140785995907697)
                ·
                  refine ⟨245922088605589496930773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327896118140785995907697 245922088605589496930773)
                  ·
                    rfl

theorem cell20_538798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_538798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538798 prefixEnd_538798 := by exact prefixLift 538798
  have htrace : WordTrace (prefixWord ++ tailWord_538798) baseStart_538798 baseEnd_538798 := by
    simpa [prefixWord, tailWord_538798, baseEnd_538798] using wordTrace_append hprefix tailTrace_538798
  have hstable : (prefixWord ++ tailWord_538798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538798).length < 2 ^ (prefixWord ++ tailWord_538798).sum := by decide
  have hdescent : baseEnd_538798 < baseStart_538798 := by decide
  rcases family_descends (prefixWord ++ tailWord_538798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538816 : List Nat := [2, 1, 1, 2, 5, 3, 1, 2, 3]
def baseStart_538816 : Nat := 118140960795 + 538816 * 2 ^ 59
def prefixEnd_538816 : Nat := 4983230072969 + 3 ^ 40 * 538816 * 2
def baseEnd_538816 : Nat := 245930304296061434330699

theorem tailTrace_538816 : CollatzResearch.WordTrace tailWord_538816 prefixEnd_538816 245930304296061434330699 := by
  unfold tailWord_538816
  simp only [CollatzResearch.WordTrace]
  refine ⟨9826117007984564645814151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13101489343979419527752201 9826117007984564645814151)
  ·
    refine ⟨14739175511976846968721227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9826117007984564645814151 14739175511976846968721227)
    ·
      refine ⟨22108763267965270453081841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14739175511976846968721227 22108763267965270453081841)
      ·
        refine ⟨16581572450973952839811381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22108763267965270453081841 16581572450973952839811381)
        ·
          refine ⟨1554522417278808078732317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16581572450973952839811381 1554522417278808078732317)
          ·
            refine ⟨582945906479553029524619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1554522417278808078732317 582945906479553029524619)
            ·
              refine ⟨874418859719329544286929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 582945906479553029524619 874418859719329544286929)
              ·
                refine ⟨655814144789497158215197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874418859719329544286929 655814144789497158215197)
                ·
                  refine ⟨245930304296061434330699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655814144789497158215197 245930304296061434330699)
                  ·
                    rfl

theorem cell20_538816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_538816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538816 prefixEnd_538816 := by exact prefixLift 538816
  have htrace : WordTrace (prefixWord ++ tailWord_538816) baseStart_538816 baseEnd_538816 := by
    simpa [prefixWord, tailWord_538816, baseEnd_538816] using wordTrace_append hprefix tailTrace_538816
  have hstable : (prefixWord ++ tailWord_538816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538816).length < 2 ^ (prefixWord ++ tailWord_538816).sum := by decide
  have hdescent : baseEnd_538816 < baseStart_538816 := by decide
  rcases family_descends (prefixWord ++ tailWord_538816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538858 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_538858 : Nat := 118140960795 + 538858 * 2 ^ 59
def prefixEnd_538858 : Nat := 4983230072969 + 3 ^ 40 * 538858 * 2
def baseEnd_538858 : Nat := 245949474240495954930527

theorem tailTrace_538858 : CollatzResearch.WordTrace tailWord_538858 prefixEnd_538858 245949474240495954930527 := by
  unfold tailWord_538858
  simp only [CollatzResearch.WordTrace]
  refine ⟨4913441470454242616164307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13102510587877980309771485 4913441470454242616164307)
  ·
    refine ⟨7370162205681363924246461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4913441470454242616164307 7370162205681363924246461)
    ·
      refine ⟨2763810827130511471592423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7370162205681363924246461 2763810827130511471592423)
      ·
        refine ⟨4145716240695767207388635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2763810827130511471592423 4145716240695767207388635)
        ·
          refine ⟨6218574361043650811082953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4145716240695767207388635 6218574361043650811082953)
          ·
            refine ⟨4663930770782738108312215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6218574361043650811082953 4663930770782738108312215)
            ·
              refine ⟨6995896156174107162468323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4663930770782738108312215 6995896156174107162468323)
              ·
                refine ⟨10493844234261160743702485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6995896156174107162468323 10493844234261160743702485)
                ·
                  refine ⟨245949474240495954930527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10493844234261160743702485 245949474240495954930527)
                  ·
                    rfl

theorem cell20_538858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_538858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538858 prefixEnd_538858 := by exact prefixLift 538858
  have htrace : WordTrace (prefixWord ++ tailWord_538858) baseStart_538858 baseEnd_538858 := by
    simpa [prefixWord, tailWord_538858, baseEnd_538858] using wordTrace_append hprefix tailTrace_538858
  have hstable : (prefixWord ++ tailWord_538858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538858).length < 2 ^ (prefixWord ++ tailWord_538858).sum := by decide
  have hdescent : baseEnd_538858 < baseStart_538858 := by decide
  rcases family_descends (prefixWord ++ tailWord_538858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538865 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 6]
def baseStart_538865 : Nat := 118140960795 + 538865 * 2 ^ 59
def prefixEnd_538865 : Nat := 4983230072969 + 3 ^ 40 * 538865 * 2
def baseEnd_538865 : Nat := 245952669231235041697165

theorem tailTrace_538865 : CollatzResearch.WordTrace tailWord_538865 prefixEnd_538865 245952669231235041697165 := by
  unfold tailWord_538865
  simp only [CollatzResearch.WordTrace]
  refine ⟨19654021192791610660162049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13102680795194407106774699 19654021192791610660162049)
  ·
    refine ⟨14740515894593707995121537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19654021192791610660162049 14740515894593707995121537)
    ·
      refine ⟨11055386920945280996341153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14740515894593707995121537 11055386920945280996341153)
      ·
        refine ⟨8291540190708960747255865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11055386920945280996341153 8291540190708960747255865)
        ·
          refine ⟨6218655143031720560441899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8291540190708960747255865 6218655143031720560441899)
          ·
            refine ⟨9327982714547580840662849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6218655143031720560441899 9327982714547580840662849)
            ·
              refine ⟨6995987035910685630497137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9327982714547580840662849 6995987035910685630497137)
              ·
                refine ⟨5246990276933014222872853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6995987035910685630497137 5246990276933014222872853)
                ·
                  refine ⟨245952669231235041697165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5246990276933014222872853 245952669231235041697165)
                  ·
                    rfl

theorem cell20_538865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_538865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538865 prefixEnd_538865 := by exact prefixLift 538865
  have htrace : WordTrace (prefixWord ++ tailWord_538865) baseStart_538865 baseEnd_538865 := by
    simpa [prefixWord, tailWord_538865, baseEnd_538865] using wordTrace_append hprefix tailTrace_538865
  have hstable : (prefixWord ++ tailWord_538865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538865).length < 2 ^ (prefixWord ++ tailWord_538865).sum := by decide
  have hdescent : baseEnd_538865 < baseStart_538865 := by decide
  rcases family_descends (prefixWord ++ tailWord_538865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538889 : List Nat := [1, 2, 1, 1, 3, 5, 2, 5]
def baseStart_538889 : Nat := 118140960795 + 538889 * 2 ^ 59
def prefixEnd_538889 : Nat := 4983230072969 + 3 ^ 40 * 538889 * 2
def baseEnd_538889 : Nat := 81987874495065874965689

theorem tailTrace_538889 : CollatzResearch.WordTrace tailWord_538889 prefixEnd_538889 81987874495065874965689 := by
  unfold tailWord_538889
  simp only [CollatzResearch.WordTrace]
  refine ⟨19654896544704662759035721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13103264363136441839357147 19654896544704662759035721)
  ·
    refine ⟨14741172408528497069276791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19654896544704662759035721 14741172408528497069276791)
    ·
      refine ⟨22111758612792745603915187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14741172408528497069276791 22111758612792745603915187)
      ·
        refine ⟨33167637919189118405872781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22111758612792745603915187 33167637919189118405872781)
        ·
          refine ⟨12437864219695919402202293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33167637919189118405872781 12437864219695919402202293)
          ·
            refine ⟨1166049770596492443956465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12437864219695919402202293 1166049770596492443956465)
            ·
              refine ⟨874537327947369332967349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1166049770596492443956465 874537327947369332967349)
              ·
                refine ⟨81987874495065874965689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 874537327947369332967349 81987874495065874965689)
                ·
                  rfl

theorem cell20_538889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 5].length) (baseStart_538889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538889 prefixEnd_538889 := by exact prefixLift 538889
  have htrace : WordTrace (prefixWord ++ tailWord_538889) baseStart_538889 baseEnd_538889 := by
    simpa [prefixWord, tailWord_538889, baseEnd_538889] using wordTrace_append hprefix tailTrace_538889
  have hstable : (prefixWord ++ tailWord_538889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538889).length < 2 ^ (prefixWord ++ tailWord_538889).sum := by decide
  have hdescent : baseEnd_538889 < baseStart_538889 := by decide
  rcases family_descends (prefixWord ++ tailWord_538889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538930 : List Nat := [3, 2, 1, 1, 5, 1, 2, 2, 3]
def baseStart_538930 : Nat := 118140960795 + 538930 * 2 ^ 59
def prefixEnd_538930 : Nat := 4983230072969 + 3 ^ 40 * 538930 * 2
def baseEnd_538930 : Nat := 245982337002383704530233

theorem tailTrace_538930 : CollatzResearch.WordTrace tailWord_538930 prefixEnd_538930 245982337002383704530233 := by
  unfold tailWord_538930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4914097984389031690319561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13104261291704084507518829 4914097984389031690319561)
  ·
    refine ⟨3685573488291773767739671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4914097984389031690319561 3685573488291773767739671)
    ·
      refine ⟨5528360232437660651609507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3685573488291773767739671 5528360232437660651609507)
      ·
        refine ⟨8292540348656490977414261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5528360232437660651609507 8292540348656490977414261)
        ·
          refine ⟨777425657686546029132587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8292540348656490977414261 777425657686546029132587)
          ·
            refine ⟨1166138486529819043698881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777425657686546029132587 1166138486529819043698881)
            ·
              refine ⟨874603864897364282774161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1166138486529819043698881 874603864897364282774161)
              ·
                refine ⟨655952898673023212080621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874603864897364282774161 655952898673023212080621)
                ·
                  refine ⟨245982337002383704530233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 655952898673023212080621 245982337002383704530233)
                  ·
                    rfl

theorem cell20_538930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_538930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538930 prefixEnd_538930 := by exact prefixLift 538930
  have htrace : WordTrace (prefixWord ++ tailWord_538930) baseStart_538930 baseEnd_538930 := by
    simpa [prefixWord, tailWord_538930, baseEnd_538930] using wordTrace_append hprefix tailTrace_538930
  have hstable : (prefixWord ++ tailWord_538930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538930).length < 2 ^ (prefixWord ++ tailWord_538930).sum := by decide
  have hdescent : baseEnd_538930 < baseStart_538930 := by decide
  rcases family_descends (prefixWord ++ tailWord_538930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_538979 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 6]
def baseStart_538979 : Nat := 118140960795 + 538979 * 2 ^ 59
def prefixEnd_538979 : Nat := 4983230072969 + 3 ^ 40 * 538979 * 2
def baseEnd_538979 : Nat := 246004701937557311896699

theorem tailTrace_538979 : CollatzResearch.WordTrace tailWord_538979 prefixEnd_538979 246004701937557311896699 := by
  unfold tailWord_538979
  simp only [CollatzResearch.WordTrace]
  refine ⟨19658179114378608129811991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13105452742919072086541327 19658179114378608129811991)
  ·
    refine ⟨29487268671567912194717987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19658179114378608129811991 29487268671567912194717987)
    ·
      refine ⟨44230903007351868292076981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29487268671567912194717987 44230903007351868292076981)
      ·
        refine ⟨4146647156939237652382217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44230903007351868292076981 4146647156939237652382217)
        ·
          refine ⟨3109985367704428239286663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4146647156939237652382217 3109985367704428239286663)
          ·
            refine ⟨4664978051556642358929995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3109985367704428239286663 4664978051556642358929995)
            ·
              refine ⟨6997467077334963538394993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4664978051556642358929995 6997467077334963538394993)
              ·
                refine ⟨5248100308001222653796245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6997467077334963538394993 5248100308001222653796245)
                ·
                  refine ⟨246004701937557311896699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5248100308001222653796245 246004701937557311896699)
                  ·
                    rfl

theorem cell20_538979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 6].length) (baseStart_538979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_538979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_538979 prefixEnd_538979 := by exact prefixLift 538979
  have htrace : WordTrace (prefixWord ++ tailWord_538979) baseStart_538979 baseEnd_538979 := by
    simpa [prefixWord, tailWord_538979, baseEnd_538979] using wordTrace_append hprefix tailTrace_538979
  have hstable : (prefixWord ++ tailWord_538979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_538979).length < 2 ^ (prefixWord ++ tailWord_538979).sum := by decide
  have hdescent : baseEnd_538979 < baseStart_538979 := by decide
  rcases family_descends (prefixWord ++ tailWord_538979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539020 : List Nat := [2, 2, 1, 2, 1, 6, 2, 4]
def baseStart_539020 : Nat := 118140960795 + 539020 * 2 ^ 59
def prefixEnd_539020 : Nat := 4983230072969 + 3 ^ 40 * 539020 * 2
def baseEnd_539020 : Nat := 82007805151581130509955

theorem tailTrace_539020 : CollatzResearch.WordTrace tailWord_539020 prefixEnd_539020 82007805151581130509955 := by
  unfold tailWord_539020
  simp only [CollatzResearch.WordTrace]
  refine ⟨9829837253615036066027257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13106449671486714754703009 9829837253615036066027257)
  ·
    refine ⟨7372377940211277049520443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9829837253615036066027257 7372377940211277049520443)
    ·
      refine ⟨11058566910316915574280665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7372377940211277049520443 11058566910316915574280665)
      ·
        refine ⟨8293925182737686680710499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11058566910316915574280665 8293925182737686680710499)
        ·
          refine ⟨12440887774106530021065749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8293925182737686680710499 12440887774106530021065749)
          ·
            refine ⟨583166614411243594737457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12440887774106530021065749 583166614411243594737457)
            ·
              refine ⟨437374960808432696053093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 583166614411243594737457 437374960808432696053093)
              ·
                refine ⟨82007805151581130509955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 437374960808432696053093 82007805151581130509955)
                ·
                  rfl

theorem cell20_539020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_539020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539020 prefixEnd_539020 := by exact prefixLift 539020
  have htrace : WordTrace (prefixWord ++ tailWord_539020) baseStart_539020 baseEnd_539020 := by
    simpa [prefixWord, tailWord_539020, baseEnd_539020] using wordTrace_append hprefix tailTrace_539020
  have hstable : (prefixWord ++ tailWord_539020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539020).length < 2 ^ (prefixWord ++ tailWord_539020).sum := by decide
  have hdescent : baseEnd_539020 < baseStart_539020 := by decide
  rcases family_descends (prefixWord ++ tailWord_539020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539061 : List Nat := [1, 3, 3, 2, 3, 2, 2, 1, 3]
def baseStart_539061 : Nat := 118140960795 + 539061 * 2 ^ 59
def prefixEnd_539061 : Nat := 4983230072969 + 3 ^ 40 * 539061 * 2
def baseEnd_539061 : Nat := 246042128971929471163031

theorem tailTrace_539061 : CollatzResearch.WordTrace tailWord_539061 prefixEnd_539061 246042128971929471163031 := by
  unfold tailWord_539061
  simp only [CollatzResearch.WordTrace]
  refine ⟨19661169900081536134297037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13107446600054357422864691 19661169900081536134297037)
  ·
    refine ⟨7372938712530576050361389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19661169900081536134297037 7372938712530576050361389)
    ·
      refine ⟨2764852017198966018885521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7372938712530576050361389 2764852017198966018885521)
      ·
        refine ⟨2073639012899224514164141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2764852017198966018885521 2073639012899224514164141)
        ·
          refine ⟨777614629837209192811553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2073639012899224514164141 777614629837209192811553)
          ·
            refine ⟨583210972377906894608665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 777614629837209192811553 583210972377906894608665)
            ·
              refine ⟨437408229283430170956499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 583210972377906894608665 437408229283430170956499)
              ·
                refine ⟨656112343925145256434749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437408229283430170956499 656112343925145256434749)
                ·
                  refine ⟨246042128971929471163031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656112343925145256434749 246042128971929471163031)
                  ·
                    rfl

theorem cell20_539061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_539061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539061 prefixEnd_539061 := by exact prefixLift 539061
  have htrace : WordTrace (prefixWord ++ tailWord_539061) baseStart_539061 baseEnd_539061 := by
    simpa [prefixWord, tailWord_539061, baseEnd_539061] using wordTrace_append hprefix tailTrace_539061
  have hstable : (prefixWord ++ tailWord_539061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539061).length < 2 ^ (prefixWord ++ tailWord_539061).sum := by decide
  have hdescent : baseEnd_539061 < baseStart_539061 := by decide
  rcases family_descends (prefixWord ++ tailWord_539061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539065 : List Nat := [1, 2, 1, 4, 3, 2, 1, 3, 3]
def baseStart_539065 : Nat := 118140960795 + 539065 * 2 ^ 59
def prefixEnd_539065 : Nat := 4983230072969 + 3 ^ 40 * 539065 * 2
def baseEnd_539065 : Nat := 246043954680923235029681

theorem tailTrace_539065 : CollatzResearch.WordTrace tailWord_539065 prefixEnd_539065 246043954680923235029681 := by
  unfold tailWord_539065
  simp only [CollatzResearch.WordTrace]
  refine ⟨19661315792067044817442649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13107543861378029878295099 19661315792067044817442649)
  ·
    refine ⟨14745986844050283613081987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19661315792067044817442649 14745986844050283613081987)
    ·
      refine ⟨22118980266075425419622981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14745986844050283613081987 22118980266075425419622981)
      ·
        refine ⟨4147308799889142266179309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22118980266075425419622981 4147308799889142266179309)
        ·
          refine ⟨1555240799958428349817241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4147308799889142266179309 1555240799958428349817241)
          ·
            refine ⟨1166430599968821262362931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1555240799958428349817241 1166430599968821262362931)
            ·
              refine ⟨1749645899953231893544397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1166430599968821262362931 1749645899953231893544397)
              ·
                refine ⟨656117212482461960079149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1749645899953231893544397 656117212482461960079149)
                ·
                  refine ⟨246043954680923235029681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656117212482461960079149 246043954680923235029681)
                  ·
                    rfl

theorem cell20_539065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_539065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539065 prefixEnd_539065 := by exact prefixLift 539065
  have htrace : WordTrace (prefixWord ++ tailWord_539065) baseStart_539065 baseEnd_539065 := by
    simpa [prefixWord, tailWord_539065, baseEnd_539065] using wordTrace_append hprefix tailTrace_539065
  have hstable : (prefixWord ++ tailWord_539065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539065).length < 2 ^ (prefixWord ++ tailWord_539065).sum := by decide
  have hdescent : baseEnd_539065 < baseStart_539065 := by decide
  rcases family_descends (prefixWord ++ tailWord_539065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539103 : List Nat := [1, 1, 2, 3, 3, 3, 2, 2, 3]
def baseStart_539103 : Nat := 118140960795 + 539103 * 2 ^ 59
def prefixEnd_539103 : Nat := 4983230072969 + 3 ^ 40 * 539103 * 2
def baseEnd_539103 : Nat := 246061298916363991762859

theorem tailTrace_539103 : CollatzResearch.WordTrace tailWord_539103 prefixEnd_539103 246061298916363991762859 := by
  unfold tailWord_539103
  simp only [CollatzResearch.WordTrace]
  refine ⟨19662701765929377307325963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13108467843952918204883975 19662701765929377307325963)
  ·
    refine ⟨29494052648894065960988945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19662701765929377307325963 29494052648894065960988945)
    ·
      refine ⟨22120539486670549470741709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29494052648894065960988945 22120539486670549470741709)
      ·
        refine ⟨8295202307501456051528141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22120539486670549470741709 8295202307501456051528141)
        ·
          refine ⟨3110700865313046019323053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8295202307501456051528141 3110700865313046019323053)
          ·
            refine ⟨1166512824492392257246145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3110700865313046019323053 1166512824492392257246145)
            ·
              refine ⟨874884618369294192934609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1166512824492392257246145 874884618369294192934609)
              ·
                refine ⟨656163463776970644700957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874884618369294192934609 656163463776970644700957)
                ·
                  refine ⟨246061298916363991762859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656163463776970644700957 246061298916363991762859)
                  ·
                    rfl

theorem cell20_539103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 3].length) (baseStart_539103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539103 prefixEnd_539103 := by exact prefixLift 539103
  have htrace : WordTrace (prefixWord ++ tailWord_539103) baseStart_539103 baseEnd_539103 := by
    simpa [prefixWord, tailWord_539103, baseEnd_539103] using wordTrace_append hprefix tailTrace_539103
  have hstable : (prefixWord ++ tailWord_539103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539103).length < 2 ^ (prefixWord ++ tailWord_539103).sum := by decide
  have hdescent : baseEnd_539103 < baseStart_539103 := by decide
  rcases family_descends (prefixWord ++ tailWord_539103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539165 : List Nat := [1, 4, 2, 2, 1, 2, 2, 4, 2]
def baseStart_539165 : Nat := 118140960795 + 539165 * 2 ^ 59
def prefixEnd_539165 : Nat := 4983230072969 + 3 ^ 40 * 539165 * 2
def baseEnd_539165 : Nat := 246089597405767331695939

theorem tailTrace_539165 : CollatzResearch.WordTrace tailWord_539165 prefixEnd_539165 246089597405767331695939 := by
  unfold tailWord_539165
  simp only [CollatzResearch.WordTrace]
  refine ⟨19664963091704761896082949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13109975394469841264055299 19664963091704761896082949)
  ·
    refine ⟨3687180579694642855515553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19664963091704761896082949 3687180579694642855515553)
    ·
      refine ⟨2765385434770982141636665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3687180579694642855515553 2765385434770982141636665)
      ·
        refine ⟨2074039076078236606227499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2765385434770982141636665 2074039076078236606227499)
        ·
          refine ⟨3111058614117354909341249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2074039076078236606227499 3111058614117354909341249)
          ·
            refine ⟨2333293960588016182005937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3111058614117354909341249 2333293960588016182005937)
            ·
              refine ⟨1749970470441012136504453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2333293960588016182005937 1749970470441012136504453)
              ·
                refine ⟨328119463207689775594585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1749970470441012136504453 328119463207689775594585)
                ·
                  refine ⟨246089597405767331695939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328119463207689775594585 246089597405767331695939)
                  ·
                    rfl

theorem cell20_539165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_539165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539165 prefixEnd_539165 := by exact prefixLift 539165
  have htrace : WordTrace (prefixWord ++ tailWord_539165) baseStart_539165 baseEnd_539165 := by
    simpa [prefixWord, tailWord_539165, baseEnd_539165] using wordTrace_append hprefix tailTrace_539165
  have hstable : (prefixWord ++ tailWord_539165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539165).length < 2 ^ (prefixWord ++ tailWord_539165).sum := by decide
  have hdescent : baseEnd_539165 < baseStart_539165 := by decide
  rcases family_descends (prefixWord ++ tailWord_539165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539214 : List Nat := [4, 1, 1, 1, 1, 2, 10]
def baseStart_539214 : Nat := 118140960795 + 539214 * 2 ^ 59
def prefixEnd_539214 : Nat := 4983230072969 + 3 ^ 40 * 539214 * 2
def baseEnd_539214 : Nat := 27345773593437882118045

theorem tailTrace_539214 : CollatzResearch.WordTrace tailWord_539214 prefixEnd_539214 27345773593437882118045 := by
  unfold tailWord_539214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2458343783565905408077087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13111166845684828843077797 2458343783565905408077087)
  ·
    refine ⟨3687515675348858112115631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2458343783565905408077087 3687515675348858112115631)
    ·
      refine ⟨5531273513023287168173447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3687515675348858112115631 5531273513023287168173447)
      ·
        refine ⟨8296910269534930752260171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5531273513023287168173447 8296910269534930752260171)
        ·
          refine ⟨12445365404302396128390257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8296910269534930752260171 12445365404302396128390257)
          ·
            refine ⟨9334024053226797096292693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12445365404302396128390257 9334024053226797096292693)
            ·
              refine ⟨27345773593437882118045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9334024053226797096292693 27345773593437882118045)
              ·
                rfl

theorem cell20_539214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 10].length) (baseStart_539214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539214 prefixEnd_539214 := by exact prefixLift 539214
  have htrace : WordTrace (prefixWord ++ tailWord_539214) baseStart_539214 baseEnd_539214 := by
    simpa [prefixWord, tailWord_539214, baseEnd_539214] using wordTrace_append hprefix tailTrace_539214
  have hstable : (prefixWord ++ tailWord_539214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539214).length < 2 ^ (prefixWord ++ tailWord_539214).sum := by decide
  have hdescent : baseEnd_539214 < baseStart_539214 := by decide
  rcases family_descends (prefixWord ++ tailWord_539214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539220 : List Nat := [2, 4, 1, 1, 1, 4, 3, 2, 2]
def baseStart_539220 : Nat := 118140960795 + 539220 * 2 ^ 59
def prefixEnd_539220 : Nat := 4983230072969 + 3 ^ 40 * 539220 * 2
def baseEnd_539220 : Nat := 246114700904431584862381

theorem tailTrace_539220 : CollatzResearch.WordTrace tailWord_539220 prefixEnd_539220 246114700904431584862381 := by
  unfold tailWord_539220
  simp only [CollatzResearch.WordTrace]
  refine ⟨9833484553252753144667557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13111312737670337526223409 9833484553252753144667557)
  ·
    refine ⟨1843778353734891214625167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9833484553252753144667557 1843778353734891214625167)
    ·
      refine ⟨2765667530602336821937751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1843778353734891214625167 2765667530602336821937751)
      ·
        refine ⟨4148501295903505232906627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2765667530602336821937751 4148501295903505232906627)
        ·
          refine ⟨6222751943855257849359941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4148501295903505232906627 6222751943855257849359941)
          ·
            refine ⟨1166765989472860846754989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6222751943855257849359941 1166765989472860846754989)
            ·
              refine ⟨437537246052322817533121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1166765989472860846754989 437537246052322817533121)
              ·
                refine ⟨328152934539242113149841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437537246052322817533121 328152934539242113149841)
                ·
                  refine ⟨246114700904431584862381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328152934539242113149841 246114700904431584862381)
                  ·
                    rfl

theorem cell20_539220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_539220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539220 prefixEnd_539220 := by exact prefixLift 539220
  have htrace : WordTrace (prefixWord ++ tailWord_539220) baseStart_539220 baseEnd_539220 := by
    simpa [prefixWord, tailWord_539220, baseEnd_539220] using wordTrace_append hprefix tailTrace_539220
  have hstable : (prefixWord ++ tailWord_539220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539220).length < 2 ^ (prefixWord ++ tailWord_539220).sum := by decide
  have hdescent : baseEnd_539220 < baseStart_539220 := by decide
  rcases family_descends (prefixWord ++ tailWord_539220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539224 : List Nat := [2, 1, 2, 2, 1, 2, 2, 6, 2]
def baseStart_539224 : Nat := 118140960795 + 539224 * 2 ^ 59
def prefixEnd_539224 : Nat := 4983230072969 + 3 ^ 40 * 539224 * 2
def baseEnd_539224 : Nat := 246116526613425348729031

theorem tailTrace_539224 : CollatzResearch.WordTrace tailWord_539224 prefixEnd_539224 246116526613425348729031 := by
  unfold tailWord_539224
  simp only [CollatzResearch.WordTrace]
  refine ⟨9833557499245507486240363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13111409998994009981653817 9833557499245507486240363)
  ·
    refine ⟨14750336248868261229360545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9833557499245507486240363 14750336248868261229360545)
    ·
      refine ⟨11062752186651195922020409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14750336248868261229360545 11062752186651195922020409)
      ·
        refine ⟨8297064139988396941515307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11062752186651195922020409 8297064139988396941515307)
        ·
          refine ⟨12445596209982595412272961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8297064139988396941515307 12445596209982595412272961)
          ·
            refine ⟨9334197157486946559204721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12445596209982595412272961 9334197157486946559204721)
            ·
              refine ⟨7000647868115209919403541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9334197157486946559204721 7000647868115209919403541)
              ·
                refine ⟨328155368817900464972041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7000647868115209919403541 328155368817900464972041)
                ·
                  refine ⟨246116526613425348729031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328155368817900464972041 246116526613425348729031)
                  ·
                    rfl

theorem cell20_539224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 6, 2].length) (baseStart_539224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539224 prefixEnd_539224 := by exact prefixLift 539224
  have htrace : WordTrace (prefixWord ++ tailWord_539224) baseStart_539224 baseEnd_539224 := by
    simpa [prefixWord, tailWord_539224, baseEnd_539224] using wordTrace_append hprefix tailTrace_539224
  have hstable : (prefixWord ++ tailWord_539224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539224).length < 2 ^ (prefixWord ++ tailWord_539224).sum := by decide
  have hdescent : baseEnd_539224 < baseStart_539224 := by decide
  rcases family_descends (prefixWord ++ tailWord_539224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539230 : List Nat := [4, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_539230 : Nat := 118140960795 + 539230 * 2 ^ 59
def prefixEnd_539230 : Nat := 4983230072969 + 3 ^ 40 * 539230 * 2
def baseEnd_539230 : Nat := 246119265176915994529007

theorem tailTrace_539230 : CollatzResearch.WordTrace tailWord_539230 prefixEnd_539230 246119265176915994529007 := by
  unfold tailWord_539230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2458416729558659749649893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13111555890979518664799429 2458416729558659749649893)
  ·
    refine ⟨460953136792248703059355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2458416729558659749649893 460953136792248703059355)
    ·
      refine ⟨691429705188373054589033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 460953136792248703059355 691429705188373054589033)
      ·
        refine ⟨518572278891279790941775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 691429705188373054589033 518572278891279790941775)
        ·
          refine ⟨777858418336919686412663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518572278891279790941775 777858418336919686412663)
          ·
            refine ⟨1166787627505379529618995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777858418336919686412663 1166787627505379529618995)
            ·
              refine ⟨1750181441258069294428493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1166787627505379529618995 1750181441258069294428493)
              ·
                refine ⟨656318040471775985410685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1750181441258069294428493 656318040471775985410685)
                ·
                  refine ⟨246119265176915994529007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656318040471775985410685 246119265176915994529007)
                  ·
                    rfl

theorem cell20_539230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_539230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539230 prefixEnd_539230 := by exact prefixLift 539230
  have htrace : WordTrace (prefixWord ++ tailWord_539230) baseStart_539230 baseEnd_539230 := by
    simpa [prefixWord, tailWord_539230, baseEnd_539230] using wordTrace_append hprefix tailTrace_539230
  have hstable : (prefixWord ++ tailWord_539230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539230).length < 2 ^ (prefixWord ++ tailWord_539230).sum := by decide
  have hdescent : baseEnd_539230 < baseStart_539230 := by decide
  rcases family_descends (prefixWord ++ tailWord_539230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539259 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 5]
def baseStart_539259 : Nat := 118140960795 + 539259 * 2 ^ 59
def prefixEnd_539259 : Nat := 4983230072969 + 3 ^ 40 * 539259 * 2
def baseEnd_539259 : Nat := 246132501567120782562221

theorem tailTrace_539259 : CollatzResearch.WordTrace tailWord_539259 prefixEnd_539259 246132501567120782562221 := by
  unfold tailWord_539259
  simp only [CollatzResearch.WordTrace]
  refine ⟨19668391553364215950004831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13112261035576143966669887 19668391553364215950004831)
  ·
    refine ⟨29502587330046323925007247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19668391553364215950004831 29502587330046323925007247)
    ·
      refine ⟨44253880995069485887510871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29502587330046323925007247 44253880995069485887510871)
      ·
        refine ⟨66380821492604228831266307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44253880995069485887510871 66380821492604228831266307)
        ·
          refine ⟨99571232238906343246899461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66380821492604228831266307 99571232238906343246899461)
          ·
            refine ⟨18669606044794939358793649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99571232238906343246899461 18669606044794939358793649)
            ·
              refine ⟨14002204533596204519095237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18669606044794939358793649 14002204533596204519095237)
              ·
                refine ⟨2625413350049288347330357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14002204533596204519095237 2625413350049288347330357)
                ·
                  refine ⟨246132501567120782562221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2625413350049288347330357 246132501567120782562221)
                  ·
                    rfl

theorem cell20_539259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_539259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539259 prefixEnd_539259 := by exact prefixLift 539259
  have htrace : WordTrace (prefixWord ++ tailWord_539259) baseStart_539259 baseEnd_539259 := by
    simpa [prefixWord, tailWord_539259, baseEnd_539259] using wordTrace_append hprefix tailTrace_539259
  have hstable : (prefixWord ++ tailWord_539259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539259).length < 2 ^ (prefixWord ++ tailWord_539259).sum := by decide
  have hdescent : baseEnd_539259 < baseStart_539259 := by decide
  rcases family_descends (prefixWord ++ tailWord_539259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539303 : List Nat := [1, 1, 6, 3, 1, 1, 3, 4]
def baseStart_539303 : Nat := 118140960795 + 539303 * 2 ^ 59
def prefixEnd_539303 : Nat := 4983230072969 + 3 ^ 40 * 539303 * 2
def baseEnd_539303 : Nat := 82050861455350728365125

theorem tailTrace_539303 : CollatzResearch.WordTrace tailWord_539303 prefixEnd_539303 82050861455350728365125 := by
  unfold tailWord_539303
  simp only [CollatzResearch.WordTrace]
  refine ⟨19669996365204811464606563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13113330910136540976404375 19669996365204811464606563)
  ·
    refine ⟨29504994547807217196909845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19669996365204811464606563 29504994547807217196909845)
    ·
      refine ⟨1383046619428463306105149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29504994547807217196909845 1383046619428463306105149)
      ·
        refine ⟨518642482285673739789431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1383046619428463306105149 518642482285673739789431)
        ·
          refine ⟨777963723428510609684147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518642482285673739789431 777963723428510609684147)
          ·
            refine ⟨1166945585142765914526221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777963723428510609684147 1166945585142765914526221)
            ·
              refine ⟨437604594428537217947333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1166945585142765914526221 437604594428537217947333)
              ·
                refine ⟨82050861455350728365125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 437604594428537217947333 82050861455350728365125)
                ·
                  rfl

theorem cell20_539303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 4].length) (baseStart_539303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539303 prefixEnd_539303 := by exact prefixLift 539303
  have htrace : WordTrace (prefixWord ++ tailWord_539303) baseStart_539303 baseEnd_539303 := by
    simpa [prefixWord, tailWord_539303, baseEnd_539303] using wordTrace_append hprefix tailTrace_539303
  have hstable : (prefixWord ++ tailWord_539303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539303).length < 2 ^ (prefixWord ++ tailWord_539303).sum := by decide
  have hdescent : baseEnd_539303 < baseStart_539303 := by decide
  rcases family_descends (prefixWord ++ tailWord_539303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539317 : List Nat := [1, 3, 3, 3, 1, 1, 1, 5, 2]
def baseStart_539317 : Nat := 118140960795 + 539317 * 2 ^ 59
def prefixEnd_539317 : Nat := 4983230072969 + 3 ^ 40 * 539317 * 2
def baseEnd_539317 : Nat := 246158974347530358628651

theorem tailTrace_539317 : CollatzResearch.WordTrace tailWord_539317 prefixEnd_539317 246158974347530358628651 := by
  unfold tailWord_539317
  simp only [CollatzResearch.WordTrace]
  refine ⟨19670506987154091855616205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13113671324769394570410803 19670506987154091855616205)
  ·
    refine ⟨7376440120182784445856077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19670506987154091855616205 7376440120182784445856077)
    ·
      refine ⟨2766165045068544167196029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7376440120182784445856077 2766165045068544167196029)
      ·
        refine ⟨1037311891900704062698511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2766165045068544167196029 1037311891900704062698511)
        ·
          refine ⟨1555967837851056094047767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1037311891900704062698511 1555967837851056094047767)
          ·
            refine ⟨2333951756776584141071651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1555967837851056094047767 2333951756776584141071651)
            ·
              refine ⟨3500927635164876211607477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2333951756776584141071651 3500927635164876211607477)
              ·
                refine ⟨328211965796707144838201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3500927635164876211607477 328211965796707144838201)
                ·
                  refine ⟨246158974347530358628651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328211965796707144838201 246158974347530358628651)
                  ·
                    rfl

theorem cell20_539317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_539317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539317 prefixEnd_539317 := by exact prefixLift 539317
  have htrace : WordTrace (prefixWord ++ tailWord_539317) baseStart_539317 baseEnd_539317 := by
    simpa [prefixWord, tailWord_539317, baseEnd_539317] using wordTrace_append hprefix tailTrace_539317
  have hstable : (prefixWord ++ tailWord_539317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539317).length < 2 ^ (prefixWord ++ tailWord_539317).sum := by decide
  have hdescent : baseEnd_539317 < baseStart_539317 := by decide
  rcases family_descends (prefixWord ++ tailWord_539317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539328 : List Nat := [2, 1, 1, 2, 4, 3, 7]
def baseStart_539328 : Nat := 118140960795 + 539328 * 2 ^ 59
def prefixEnd_539328 : Nat := 4983230072969 + 3 ^ 40 * 539328 * 2
def baseEnd_539328 : Nat := 27351555005251467695771

theorem tailTrace_539328 : CollatzResearch.WordTrace tailWord_539328 prefixEnd_539328 27351555005251467695771 := by
  unfold tailWord_539328
  simp only [CollatzResearch.WordTrace]
  refine ⟨9835454095057120367133319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13113938793409493822844425 9835454095057120367133319)
  ·
    refine ⟨14753181142585680550699979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9835454095057120367133319 14753181142585680550699979)
    ·
      refine ⟨22129771713878520826049969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14753181142585680550699979 22129771713878520826049969)
      ·
        refine ⟨16597328785408890619537477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22129771713878520826049969 16597328785408890619537477)
        ·
          refine ⟨3111999147264166991163277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16597328785408890619537477 3111999147264166991163277)
          ·
            refine ⟨1166999680224062621686229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3111999147264166991163277 1166999680224062621686229)
            ·
              refine ⟨27351555005251467695771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1166999680224062621686229 27351555005251467695771)
              ·
                rfl

theorem cell20_539328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 7].length) (baseStart_539328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539328 prefixEnd_539328 := by exact prefixLift 539328
  have htrace : WordTrace (prefixWord ++ tailWord_539328) baseStart_539328 baseEnd_539328 := by
    simpa [prefixWord, tailWord_539328, baseEnd_539328] using wordTrace_append hprefix tailTrace_539328
  have hstable : (prefixWord ++ tailWord_539328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539328).length < 2 ^ (prefixWord ++ tailWord_539328).sum := by decide
  have hdescent : baseEnd_539328 < baseStart_539328 := by decide
  rcases family_descends (prefixWord ++ tailWord_539328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539338 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_539338 : Nat := 118140960795 + 539338 * 2 ^ 59
def prefixEnd_539338 : Nat := 4983230072969 + 3 ^ 40 * 539338 * 2
def baseEnd_539338 : Nat := 246168559319747618928565

theorem tailTrace_539338 : CollatzResearch.WordTrace tailWord_539338 prefixEnd_539338 246168559319747618928565 := by
  unfold tailWord_539338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4917818230019503110532667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13114181946718674961420445 4917818230019503110532667)
  ·
    refine ⟨7376727345029254665799001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4917818230019503110532667 7376727345029254665799001)
    ·
      refine ⟨5532545508771940999349251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7376727345029254665799001 5532545508771940999349251)
      ·
        refine ⟨8298818263157911499023877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5532545508771940999349251 8298818263157911499023877)
        ·
          refine ⟨1556028424342108406066977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8298818263157911499023877 1556028424342108406066977)
          ·
            refine ⟨1167021318256581304550233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1556028424342108406066977 1167021318256581304550233)
            ·
              refine ⟨875265988692435978412675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1167021318256581304550233 875265988692435978412675)
              ·
                refine ⟨1312898983038653967619013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875265988692435978412675 1312898983038653967619013)
                ·
                  refine ⟨246168559319747618928565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1312898983038653967619013 246168559319747618928565)
                  ·
                    rfl

theorem cell20_539338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_539338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539338 prefixEnd_539338 := by exact prefixLift 539338
  have htrace : WordTrace (prefixWord ++ tailWord_539338) baseStart_539338 baseEnd_539338 := by
    simpa [prefixWord, tailWord_539338, baseEnd_539338] using wordTrace_append hprefix tailTrace_539338
  have hstable : (prefixWord ++ tailWord_539338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539338).length < 2 ^ (prefixWord ++ tailWord_539338).sum := by decide
  have hdescent : baseEnd_539338 < baseStart_539338 := by decide
  rcases family_descends (prefixWord ++ tailWord_539338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539359 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 4]
def baseStart_539359 : Nat := 118140960795 + 539359 * 2 ^ 59
def prefixEnd_539359 : Nat := 4983230072969 + 3 ^ 40 * 539359 * 2
def baseEnd_539359 : Nat := 246178144291964879228479

theorem tailTrace_539359 : CollatzResearch.WordTrace tailWord_539359 prefixEnd_539359 246178144291964879228479 := by
  unfold tailWord_539359
  simp only [CollatzResearch.WordTrace]
  refine ⟨19672038853001933028645131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13114692568667955352430087 19672038853001933028645131)
  ·
    refine ⟨29508058279502899542967697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19672038853001933028645131 29508058279502899542967697)
    ·
      refine ⟨22131043709627174657225773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29508058279502899542967697 22131043709627174657225773)
      ·
        refine ⟨8299141391110190496459665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22131043709627174657225773 8299141391110190496459665)
        ·
          refine ⟨6224356043332642872344749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8299141391110190496459665 6224356043332642872344749)
          ·
            refine ⟨2334133516249741077129281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6224356043332642872344749 2334133516249741077129281)
            ·
              refine ⟨1750600137187305807846961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2334133516249741077129281 1750600137187305807846961)
              ·
                refine ⟨1312950102890479355885221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1750600137187305807846961 1312950102890479355885221)
                ·
                  refine ⟨246178144291964879228479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1312950102890479355885221 246178144291964879228479)
                  ·
                    rfl

theorem cell20_539359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_539359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539359 prefixEnd_539359 := by exact prefixLift 539359
  have htrace : WordTrace (prefixWord ++ tailWord_539359) baseStart_539359 baseEnd_539359 := by
    simpa [prefixWord, tailWord_539359, baseEnd_539359] using wordTrace_append hprefix tailTrace_539359
  have hstable : (prefixWord ++ tailWord_539359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539359).length < 2 ^ (prefixWord ++ tailWord_539359).sum := by decide
  have hdescent : baseEnd_539359 < baseStart_539359 := by decide
  rcases family_descends (prefixWord ++ tailWord_539359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539444 : List Nat := [2, 5, 1, 1, 4, 1, 2, 2, 2]
def baseStart_539444 : Nat := 118140960795 + 539444 * 2 ^ 59
def prefixEnd_539444 : Nat := 4983230072969 + 3 ^ 40 * 539444 * 2
def baseEnd_539444 : Nat := 246216940608082361394799

theorem tailTrace_539444 : CollatzResearch.WordTrace tailWord_539444 prefixEnd_539444 246216940608082361394799 := by
  unfold tailWord_539444
  simp only [CollatzResearch.WordTrace]
  refine ⟨9837569528846996272744693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13116759371795995030326257 9837569528846996272744693)
  ·
    refine ⟨922272143329405900569815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9837569528846996272744693 922272143329405900569815)
    ·
      refine ⟨1383408214994108850854723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 922272143329405900569815 1383408214994108850854723)
      ·
        refine ⟨2075112322491163276282085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1383408214994108850854723 2075112322491163276282085)
        ·
          refine ⟨389083560467093114302891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2075112322491163276282085 389083560467093114302891)
          ·
            refine ⟨583625340700639671454337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389083560467093114302891 583625340700639671454337)
            ·
              refine ⟨437719005525479753590753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 583625340700639671454337 437719005525479753590753)
              ·
                refine ⟨328289254144109815193065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437719005525479753590753 328289254144109815193065)
                ·
                  refine ⟨246216940608082361394799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328289254144109815193065 246216940608082361394799)
                  ·
                    rfl

theorem cell20_539444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_539444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539444 prefixEnd_539444 := by exact prefixLift 539444
  have htrace : WordTrace (prefixWord ++ tailWord_539444) baseStart_539444 baseEnd_539444 := by
    simpa [prefixWord, tailWord_539444, baseEnd_539444] using wordTrace_append hprefix tailTrace_539444
  have hstable : (prefixWord ++ tailWord_539444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539444).length < 2 ^ (prefixWord ++ tailWord_539444).sum := by decide
  have hdescent : baseEnd_539444 < baseStart_539444 := by decide
  rcases family_descends (prefixWord ++ tailWord_539444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539445 : List Nat := [1, 3, 3, 1, 3, 2, 2, 2, 3]
def baseStart_539445 : Nat := 118140960795 + 539445 * 2 ^ 59
def prefixEnd_539445 : Nat := 4983230072969 + 3 ^ 40 * 539445 * 2
def baseEnd_539445 : Nat := 246217397035330802361461

theorem tailTrace_539445 : CollatzResearch.WordTrace tailWord_539445 prefixEnd_539445 246217397035330802361461 := by
  unfold tailWord_539445
  simp only [CollatzResearch.WordTrace]
  refine ⟨19675175530690369716275789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13116783687126913144183859 19675175530690369716275789)
  ·
    refine ⟨7378190824008888643603421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19675175530690369716275789 7378190824008888643603421)
    ·
      refine ⟨2766821559003333241351283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7378190824008888643603421 2766821559003333241351283)
      ·
        refine ⟨4150232338504999862026925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2766821559003333241351283 4150232338504999862026925)
        ·
          refine ⟨1556337126939374948260097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4150232338504999862026925 1556337126939374948260097)
          ·
            refine ⟨1167252845204531211195073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1556337126939374948260097 1167252845204531211195073)
            ·
              refine ⟨875439633903398408396305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1167252845204531211195073 875439633903398408396305)
              ·
                refine ⟨656579725427548806297229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875439633903398408396305 656579725427548806297229)
                ·
                  refine ⟨246217397035330802361461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656579725427548806297229 246217397035330802361461)
                  ·
                    rfl

theorem cell20_539445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_539445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539445 prefixEnd_539445 := by exact prefixLift 539445
  have htrace : WordTrace (prefixWord ++ tailWord_539445) baseStart_539445 baseEnd_539445 := by
    simpa [prefixWord, tailWord_539445, baseEnd_539445] using wordTrace_append hprefix tailTrace_539445
  have hstable : (prefixWord ++ tailWord_539445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539445).length < 2 ^ (prefixWord ++ tailWord_539445).sum := by decide
  have hdescent : baseEnd_539445 < baseStart_539445 := by decide
  rcases family_descends (prefixWord ++ tailWord_539445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539456 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_539456 : Nat := 118140960795 + 539456 * 2 ^ 59
def prefixEnd_539456 : Nat := 4983230072969 + 3 ^ 40 * 539456 * 2
def baseEnd_539456 : Nat := 246222417735063652994749

theorem tailTrace_539456 : CollatzResearch.WordTrace tailWord_539456 prefixEnd_539456 246222417735063652994749 := by
  unfold tailWord_539456
  simp only [CollatzResearch.WordTrace]
  refine ⟨9837788366825259297463111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13117051155767012396617481 9837788366825259297463111)
  ·
    refine ⟨14756682550237888946194667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9837788366825259297463111 14756682550237888946194667)
    ·
      refine ⟨22135023825356833419292001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14756682550237888946194667 22135023825356833419292001)
      ·
        refine ⟨16601267869017625064469001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22135023825356833419292001 16601267869017625064469001)
        ·
          refine ⟨12450950901763218798351751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16601267869017625064469001 12450950901763218798351751)
          ·
            refine ⟨18676426352644828197527627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12450950901763218798351751 18676426352644828197527627)
            ·
              refine ⟨28014639528967242296291441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18676426352644828197527627 28014639528967242296291441)
              ·
                refine ⟨21010979646725431722218581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28014639528967242296291441 21010979646725431722218581)
                ·
                  refine ⟨246222417735063652994749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21010979646725431722218581 246222417735063652994749)
                  ·
                    rfl

theorem cell20_539456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_539456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539456 prefixEnd_539456 := by exact prefixLift 539456
  have htrace : WordTrace (prefixWord ++ tailWord_539456) baseStart_539456 baseEnd_539456 := by
    simpa [prefixWord, tailWord_539456, baseEnd_539456] using wordTrace_append hprefix tailTrace_539456
  have hstable : (prefixWord ++ tailWord_539456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539456).length < 2 ^ (prefixWord ++ tailWord_539456).sum := by decide
  have hdescent : baseEnd_539456 < baseStart_539456 := by decide
  rcases family_descends (prefixWord ++ tailWord_539456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539469 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 4]
def baseStart_539469 : Nat := 118140960795 + 539469 * 2 ^ 59
def prefixEnd_539469 : Nat := 4983230072969 + 3 ^ 40 * 539469 * 2
def baseEnd_539469 : Nat := 246228351289293385561363

theorem tailTrace_539469 : CollatzResearch.WordTrace tailWord_539469 prefixEnd_539469 246228351289293385561363 := by
  unfold tailWord_539469
  simp only [CollatzResearch.WordTrace]
  refine ⟨19676050882603421815149461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13117367255068947876766307 19676050882603421815149461)
  ·
    refine ⟨922314885122035397585131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19676050882603421815149461 922314885122035397585131)
    ·
      refine ⟨1383472327683053096377697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 922314885122035397585131 1383472327683053096377697)
      ·
        refine ⟨1037604245762289822283273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1383472327683053096377697 1037604245762289822283273)
        ·
          refine ⟨778203184321717366712455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1037604245762289822283273 778203184321717366712455)
          ·
            refine ⟨1167304776482576050068683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778203184321717366712455 1167304776482576050068683)
            ·
              refine ⟨1750957164723864075103025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167304776482576050068683 1750957164723864075103025)
              ·
                refine ⟨1313217873542898056327269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1750957164723864075103025 1313217873542898056327269)
                ·
                  refine ⟨246228351289293385561363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1313217873542898056327269 246228351289293385561363)
                  ·
                    rfl

theorem cell20_539469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_539469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539469 prefixEnd_539469 := by exact prefixLift 539469
  have htrace : WordTrace (prefixWord ++ tailWord_539469) baseStart_539469 baseEnd_539469 := by
    simpa [prefixWord, tailWord_539469, baseEnd_539469] using wordTrace_append hprefix tailTrace_539469
  have hstable : (prefixWord ++ tailWord_539469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539469).length < 2 ^ (prefixWord ++ tailWord_539469).sum := by decide
  have hdescent : baseEnd_539469 < baseStart_539469 := by decide
  rcases family_descends (prefixWord ++ tailWord_539469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539476 : List Nat := [2, 4, 1, 1, 4, 1, 3, 4]
def baseStart_539476 : Nat := 118140960795 + 539476 * 2 ^ 59
def prefixEnd_539476 : Nat := 4983230072969 + 3 ^ 40 * 539476 * 2
def baseEnd_539476 : Nat := 82077182093344157442667

theorem tailTrace_539476 : CollatzResearch.WordTrace tailWord_539476 prefixEnd_539476 82077182093344157442667 := by
  unfold tailWord_539476
  simp only [CollatzResearch.WordTrace]
  refine ⟨9838153096789031005327141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13117537462385374673769521 9838153096789031005327141)
  ·
    refine ⟨1844653705647943313498839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9838153096789031005327141 1844653705647943313498839)
    ·
      refine ⟨2766980558471914970248259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1844653705647943313498839 2766980558471914970248259)
      ·
        refine ⟨4150470837707872455372389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2766980558471914970248259 4150470837707872455372389)
        ·
          refine ⟨778213282070226085382323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4150470837707872455372389 778213282070226085382323)
          ·
            refine ⟨1167319923105339128073485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778213282070226085382323 1167319923105339128073485)
            ·
              refine ⟨437744971164502173027557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1167319923105339128073485 437744971164502173027557)
              ·
                refine ⟨82077182093344157442667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 437744971164502173027557 82077182093344157442667)
                ·
                  rfl

theorem cell20_539476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_539476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539476 prefixEnd_539476 := by exact prefixLift 539476
  have htrace : WordTrace (prefixWord ++ tailWord_539476) baseStart_539476 baseEnd_539476 := by
    simpa [prefixWord, tailWord_539476, baseEnd_539476] using wordTrace_append hprefix tailTrace_539476
  have hstable : (prefixWord ++ tailWord_539476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539476).length < 2 ^ (prefixWord ++ tailWord_539476).sum := by decide
  have hdescent : baseEnd_539476 < baseStart_539476 := by decide
  rcases family_descends (prefixWord ++ tailWord_539476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539487 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 5]
def baseStart_539487 : Nat := 118140960795 + 539487 * 2 ^ 59
def prefixEnd_539487 : Nat := 4983230072969 + 3 ^ 40 * 539487 * 2
def baseEnd_539487 : Nat := 246236566979765322961289

theorem tailTrace_539487 : CollatzResearch.WordTrace tailWord_539487 prefixEnd_539487 246236566979765322961289 := by
  unfold tailWord_539487
  simp only [CollatzResearch.WordTrace]
  refine ⟨19676707396538210889304715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13117804931025473926203143 19676707396538210889304715)
  ·
    refine ⟨29515061094807316333957073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19676707396538210889304715 29515061094807316333957073)
    ·
      refine ⟨22136295821105487250467805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29515061094807316333957073 22136295821105487250467805)
      ·
        refine ⟨8301110932914557718925427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22136295821105487250467805 8301110932914557718925427)
        ·
          refine ⟨12451666399371836578388141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8301110932914557718925427 12451666399371836578388141)
          ·
            refine ⟨4669374899764438716895553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12451666399371836578388141 4669374899764438716895553)
            ·
              refine ⟨3502031174823329037671665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4669374899764438716895553 3502031174823329037671665)
              ·
                refine ⟨2626523381117496778253749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3502031174823329037671665 2626523381117496778253749)
                ·
                  refine ⟨246236566979765322961289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2626523381117496778253749 246236566979765322961289)
                  ·
                    rfl

theorem cell20_539487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_539487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539487 prefixEnd_539487 := by exact prefixLift 539487
  have htrace : WordTrace (prefixWord ++ tailWord_539487) baseStart_539487 baseEnd_539487 := by
    simpa [prefixWord, tailWord_539487, baseEnd_539487] using wordTrace_append hprefix tailTrace_539487
  have hstable : (prefixWord ++ tailWord_539487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539487).length < 2 ^ (prefixWord ++ tailWord_539487).sum := by decide
  have hdescent : baseEnd_539487 < baseStart_539487 := by decide
  rcases family_descends (prefixWord ++ tailWord_539487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539504 : List Nat := [2, 1, 1, 1, 4, 1, 5, 2, 3]
def baseStart_539504 : Nat := 118140960795 + 539504 * 2 ^ 59
def prefixEnd_539504 : Nat := 4983230072969 + 3 ^ 40 * 539504 * 2
def baseEnd_539504 : Nat := 246244326242988819394553

theorem tailTrace_539504 : CollatzResearch.WordTrace tailWord_539504 prefixEnd_539504 246244326242988819394553 := by
  unfold tailWord_539504
  simp only [CollatzResearch.WordTrace]
  refine ⟨9838663718738311396336783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13118218291651081861782377 9838663718738311396336783)
  ·
    refine ⟨14757995578107467094505175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9838663718738311396336783 14757995578107467094505175)
    ·
      refine ⟨22136993367161200641757763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14757995578107467094505175 22136993367161200641757763)
      ·
        refine ⟨33205490050741800962636645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22136993367161200641757763 33205490050741800962636645)
        ·
          refine ⟨6226029384514087680494371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33205490050741800962636645 6226029384514087680494371)
          ·
            refine ⟨9339044076771131520741557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6226029384514087680494371 9339044076771131520741557)
            ·
              refine ⟨875535382197293580069521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9339044076771131520741557 875535382197293580069521)
              ·
                refine ⟨656651536647970185052141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875535382197293580069521 656651536647970185052141)
                ·
                  refine ⟨246244326242988819394553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656651536647970185052141 246244326242988819394553)
                  ·
                    rfl

theorem cell20_539504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_539504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539504 prefixEnd_539504 := by exact prefixLift 539504
  have htrace : WordTrace (prefixWord ++ tailWord_539504) baseStart_539504 baseEnd_539504 := by
    simpa [prefixWord, tailWord_539504, baseEnd_539504] using wordTrace_append hprefix tailTrace_539504
  have hstable : (prefixWord ++ tailWord_539504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539504).length < 2 ^ (prefixWord ++ tailWord_539504).sum := by decide
  have hdescent : baseEnd_539504 < baseStart_539504 := by decide
  rcases family_descends (prefixWord ++ tailWord_539504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539615 : List Nat := [1, 1, 2, 3, 13]
def baseStart_539615 : Nat := 118140960795 + 539615 * 2 ^ 59
def prefixEnd_539615 : Nat := 4983230072969 + 3 ^ 40 * 539615 * 2
def baseEnd_539615 : Nat := 3040678884784762551779

theorem tailTrace_539615 : CollatzResearch.WordTrace tailWord_539615 prefixEnd_539615 3040678884784762551779 := by
  unfold tailWord_539615
  simp only [CollatzResearch.WordTrace]
  refine ⟨19681375940074488749964299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13120917293382992499976199 19681375940074488749964299)
  ·
    refine ⟨29522063910111733124946449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19681375940074488749964299 29522063910111733124946449)
    ·
      refine ⟨22141547932583799843709837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29522063910111733124946449 22141547932583799843709837)
      ·
        refine ⟨8303080474718924941391189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22141547932583799843709837 8303080474718924941391189)
        ·
          refine ⟨3040678884784762551779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 8303080474718924941391189 3040678884784762551779)
          ·
            rfl

theorem cell20_539615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 13].length) (baseStart_539615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539615 prefixEnd_539615 := by exact prefixLift 539615
  have htrace : WordTrace (prefixWord ++ tailWord_539615) baseStart_539615 baseEnd_539615 := by
    simpa [prefixWord, tailWord_539615, baseEnd_539615] using wordTrace_append hprefix tailTrace_539615
  have hstable : (prefixWord ++ tailWord_539615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539615).length < 2 ^ (prefixWord ++ tailWord_539615).sum := by decide
  have hdescent : baseEnd_539615 < baseStart_539615 := by decide
  rcases family_descends (prefixWord ++ tailWord_539615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539649 : List Nat := [1, 2, 4, 1, 2, 3, 3, 4]
def baseStart_539649 : Nat := 118140960795 + 539649 * 2 ^ 59
def prefixEnd_539649 : Nat := 4983230072969 + 3 ^ 40 * 539649 * 2
def baseEnd_539649 : Nat := 82103502731337586520209

theorem tailTrace_539649 : CollatzResearch.WordTrace tailWord_539649 prefixEnd_539649 82103502731337586520209 := by
  unfold tailWord_539649
  simp only [CollatzResearch.WordTrace]
  refine ⟨19682616021951312556702001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13121744014634208371134667 19682616021951312556702001)
  ·
    refine ⟨14761962016463484417526501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19682616021951312556702001 14761962016463484417526501)
    ·
      refine ⟨2767867878086903328286219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14761962016463484417526501 2767867878086903328286219)
      ·
        refine ⟨4151801817130354992429329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2767867878086903328286219 4151801817130354992429329)
        ·
          refine ⟨3113851362847766244321997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4151801817130354992429329 3113851362847766244321997)
          ·
            refine ⟨1167694261067912341620749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3113851362847766244321997 1167694261067912341620749)
            ·
              refine ⟨437885347900467128107781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1167694261067912341620749 437885347900467128107781)
              ·
                refine ⟨82103502731337586520209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 437885347900467128107781 82103502731337586520209)
                ·
                  rfl

theorem cell20_539649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 4].length) (baseStart_539649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539649 prefixEnd_539649 := by exact prefixLift 539649
  have htrace : WordTrace (prefixWord ++ tailWord_539649) baseStart_539649 baseEnd_539649 := by
    simpa [prefixWord, tailWord_539649, baseEnd_539649] using wordTrace_append hprefix tailTrace_539649
  have hstable : (prefixWord ++ tailWord_539649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539649).length < 2 ^ (prefixWord ++ tailWord_539649).sum := by decide
  have hdescent : baseEnd_539649 < baseStart_539649 := by decide
  rcases family_descends (prefixWord ++ tailWord_539649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539690 : List Nat := [3, 1, 4, 1, 3, 1, 3, 1, 3]
def baseStart_539690 : Nat := 118140960795 + 539690 * 2 ^ 59
def prefixEnd_539690 : Nat := 4983230072969 + 3 ^ 40 * 539690 * 2
def baseEnd_539690 : Nat := 246329221711198839193793

theorem tailTrace_539690 : CollatzResearch.WordTrace tailWord_539690 prefixEnd_539690 246329221711198839193793 := by
  unfold tailWord_539690
  simp only [CollatzResearch.WordTrace]
  refine ⟨4921027853700694139736131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13122740943201851039296349 4921027853700694139736131)
  ·
    refine ⟨7381541780551041209604197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4921027853700694139736131 7381541780551041209604197)
    ·
      refine ⟨1384039083853320226800787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7381541780551041209604197 1384039083853320226800787)
      ·
        refine ⟨2076058625779980340201181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384039083853320226800787 2076058625779980340201181)
        ·
          refine ⟨778521984667492627575443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2076058625779980340201181 778521984667492627575443)
          ·
            refine ⟨1167782977001238941363165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778521984667492627575443 1167782977001238941363165)
            ·
              refine ⟨437918616375464603011187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1167782977001238941363165 437918616375464603011187)
              ·
                refine ⟨656877924563196904516781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437918616375464603011187 656877924563196904516781)
                ·
                  refine ⟨246329221711198839193793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 656877924563196904516781 246329221711198839193793)
                  ·
                    rfl

theorem cell20_539690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_539690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539690 prefixEnd_539690 := by exact prefixLift 539690
  have htrace : WordTrace (prefixWord ++ tailWord_539690) baseStart_539690 baseEnd_539690 := by
    simpa [prefixWord, tailWord_539690, baseEnd_539690] using wordTrace_append hprefix tailTrace_539690
  have hstable : (prefixWord ++ tailWord_539690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539690).length < 2 ^ (prefixWord ++ tailWord_539690).sum := by decide
  have hdescent : baseEnd_539690 < baseStart_539690 := by decide
  rcases family_descends (prefixWord ++ tailWord_539690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539691 : List Nat := [1, 1, 1, 1, 2, 1, 6, 7]
def baseStart_539691 : Nat := 118140960795 + 539691 * 2 ^ 59
def prefixEnd_539691 : Nat := 4983230072969 + 3 ^ 40 * 539691 * 2
def baseEnd_539691 : Nat := 82109892712815760053485

theorem tailTrace_539691 : CollatzResearch.WordTrace tailWord_539691 prefixEnd_539691 82109892712815760053485 := by
  unfold tailWord_539691
  simp only [CollatzResearch.WordTrace]
  refine ⟨19684147887799153729730927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13122765258532769153153951 19684147887799153729730927)
  ·
    refine ⟨29526221831698730594596391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19684147887799153729730927 29526221831698730594596391)
    ·
      refine ⟨44289332747548095891894587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29526221831698730594596391 44289332747548095891894587)
      ·
        refine ⟨66433999121322143837841881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44289332747548095891894587 66433999121322143837841881)
        ·
          refine ⟨49825499340991607878381411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66433999121322143837841881 49825499340991607878381411)
          ·
            refine ⟨74738249011487411817572117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49825499340991607878381411 74738249011487411817572117)
            ·
              refine ⟨3503355422413472428948693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74738249011487411817572117 3503355422413472428948693)
              ·
                refine ⟨82109892712815760053485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3503355422413472428948693 82109892712815760053485)
                ·
                  rfl

theorem cell20_539691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 7].length) (baseStart_539691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539691 prefixEnd_539691 := by exact prefixLift 539691
  have htrace : WordTrace (prefixWord ++ tailWord_539691) baseStart_539691 baseEnd_539691 := by
    simpa [prefixWord, tailWord_539691, baseEnd_539691] using wordTrace_append hprefix tailTrace_539691
  have hstable : (prefixWord ++ tailWord_539691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539691).length < 2 ^ (prefixWord ++ tailWord_539691).sum := by decide
  have hdescent : baseEnd_539691 < baseStart_539691 := by decide
  rcases family_descends (prefixWord ++ tailWord_539691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539708 : List Nat := [2, 2, 2, 2, 2, 3, 1, 6]
def baseStart_539708 : Nat := 118140960795 + 539708 * 2 ^ 59
def prefixEnd_539708 : Nat := 4983230072969 + 3 ^ 40 * 539708 * 2
def baseEnd_539708 : Nat := 82112479133890258864573

theorem tailTrace_539708 : CollatzResearch.WordTrace tailWord_539708 prefixEnd_539708 82112479133890258864573 := by
  unfold tailWord_539708
  simp only [CollatzResearch.WordTrace]
  refine ⟨9842383964368782816549889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13123178619158377088733185 9842383964368782816549889)
  ·
    refine ⟨7381787973276587112412417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9842383964368782816549889 7381787973276587112412417)
    ·
      refine ⟨5536340979957440334309313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7381787973276587112412417 5536340979957440334309313)
      ·
        refine ⟨4152255734968080250731985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5536340979957440334309313 4152255734968080250731985)
        ·
          refine ⟨3114191801226060188048989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4152255734968080250731985 3114191801226060188048989)
          ·
            refine ⟨1167821925459772570518371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3114191801226060188048989 1167821925459772570518371)
            ·
              refine ⟨1751732888189658855777557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1167821925459772570518371 1751732888189658855777557)
              ·
                refine ⟨82112479133890258864573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1751732888189658855777557 82112479133890258864573)
                ·
                  rfl

theorem cell20_539708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_539708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539708 prefixEnd_539708 := by exact prefixLift 539708
  have htrace : WordTrace (prefixWord ++ tailWord_539708) baseStart_539708 baseEnd_539708 := by
    simpa [prefixWord, tailWord_539708, baseEnd_539708] using wordTrace_append hprefix tailTrace_539708
  have hstable : (prefixWord ++ tailWord_539708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539708).length < 2 ^ (prefixWord ++ tailWord_539708).sum := by decide
  have hdescent : baseEnd_539708 < baseStart_539708 := by decide
  rcases family_descends (prefixWord ++ tailWord_539708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539722 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_539722 : Nat := 118140960795 + 539722 * 2 ^ 59
def prefixEnd_539722 : Nat := 4983230072969 + 3 ^ 40 * 539722 * 2
def baseEnd_539722 : Nat := 246343827383148950126995

theorem tailTrace_539722 : CollatzResearch.WordTrace tailWord_539722 prefixEnd_539722 246343827383148950126995 := by
  unfold tailWord_539722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4921319637671711506027355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13123519033791230682739613 4921319637671711506027355)
  ·
    refine ⟨7381979456507567259041033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4921319637671711506027355 7381979456507567259041033)
    ·
      refine ⟨5536484592380675444280775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7381979456507567259041033 5536484592380675444280775)
      ·
        refine ⟨8304726888571013166421163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5536484592380675444280775 8304726888571013166421163)
        ·
          refine ⟨12457090332856519749631745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8304726888571013166421163 12457090332856519749631745)
          ·
            refine ⟨9342817749642389812223809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12457090332856519749631745 9342817749642389812223809)
            ·
              refine ⟨7007113312231792359167857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9342817749642389812223809 7007113312231792359167857)
              ·
                refine ⟨5255334984173844269375893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7007113312231792359167857 5255334984173844269375893)
                ·
                  refine ⟨246343827383148950126995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5255334984173844269375893 246343827383148950126995)
                  ·
                    rfl

theorem cell20_539722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_539722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539722 prefixEnd_539722 := by exact prefixLift 539722
  have htrace : WordTrace (prefixWord ++ tailWord_539722) baseStart_539722 baseEnd_539722 := by
    simpa [prefixWord, tailWord_539722, baseEnd_539722] using wordTrace_append hprefix tailTrace_539722
  have hstable : (prefixWord ++ tailWord_539722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539722).length < 2 ^ (prefixWord ++ tailWord_539722).sum := by decide
  have hdescent : baseEnd_539722 < baseStart_539722 := by decide
  rcases family_descends (prefixWord ++ tailWord_539722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539725 : List Nat := [1, 6, 1, 1, 1, 4, 6]
def baseStart_539725 : Nat := 118140960795 + 539725 * 2 ^ 59
def prefixEnd_539725 : Nat := 4983230072969 + 3 ^ 40 * 539725 * 2
def baseEnd_539725 : Nat := 27371688518321585891887

theorem tailTrace_539725 : CollatzResearch.WordTrace tailWord_539725 prefixEnd_539725 27371688518321585891887 := by
  unfold tailWord_539725
  simp only [CollatzResearch.WordTrace]
  refine ⟨19685387969675977536468629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13123591979783985024312419 19685387969675977536468629)
  ·
    refine ⟨922752561078561447021967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19685387969675977536468629 922752561078561447021967)
    ·
      refine ⟨1384128841617842170532951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 922752561078561447021967 1384128841617842170532951)
      ·
        refine ⟨2076193262426763255799427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384128841617842170532951 2076193262426763255799427)
        ·
          refine ⟨3114289893640144883699141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2076193262426763255799427 3114289893640144883699141)
          ·
            refine ⟨583929355057527165693589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3114289893640144883699141 583929355057527165693589)
            ·
              refine ⟨27371688518321585891887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 583929355057527165693589 27371688518321585891887)
              ·
                rfl

theorem cell20_539725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 6].length) (baseStart_539725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539725 prefixEnd_539725 := by exact prefixLift 539725
  have htrace : WordTrace (prefixWord ++ tailWord_539725) baseStart_539725 baseEnd_539725 := by
    simpa [prefixWord, tailWord_539725, baseEnd_539725] using wordTrace_append hprefix tailTrace_539725
  have hstable : (prefixWord ++ tailWord_539725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539725).length < 2 ^ (prefixWord ++ tailWord_539725).sum := by decide
  have hdescent : baseEnd_539725 < baseStart_539725 := by decide
  rcases family_descends (prefixWord ++ tailWord_539725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539729 : List Nat := [1, 2, 2, 1, 3, 1, 10]
def baseStart_539729 : Nat := 118140960795 + 539729 * 2 ^ 59
def prefixEnd_539729 : Nat := 4983230072969 + 3 ^ 40 * 539729 * 2
def baseEnd_539729 : Nat := 27371891374876448543737

theorem tailTrace_539729 : CollatzResearch.WordTrace tailWord_539729 prefixEnd_539729 27371891374876448543737 := by
  unfold tailWord_539729
  simp only [CollatzResearch.WordTrace]
  refine ⟨19685533861661486219614241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13123689241107657479742827 19685533861661486219614241)
  ·
    refine ⟨14764150396246114664710681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19685533861661486219614241 14764150396246114664710681)
    ·
      refine ⟨11073112797184585998533011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14764150396246114664710681 11073112797184585998533011)
      ·
        refine ⟨16609669195776878997799517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11073112797184585998533011 16609669195776878997799517)
        ·
          refine ⟨6228625948416329624174819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16609669195776878997799517 6228625948416329624174819)
          ·
            refine ⟨9342938922624494436262229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6228625948416329624174819 9342938922624494436262229)
            ·
              refine ⟨27371891374876448543737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9342938922624494436262229 27371891374876448543737)
              ·
                rfl

theorem cell20_539729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 10].length) (baseStart_539729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539729 prefixEnd_539729 := by exact prefixLift 539729
  have htrace : WordTrace (prefixWord ++ tailWord_539729) baseStart_539729 baseEnd_539729 := by
    simpa [prefixWord, tailWord_539729, baseEnd_539729] using wordTrace_append hprefix tailTrace_539729
  have hstable : (prefixWord ++ tailWord_539729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539729).length < 2 ^ (prefixWord ++ tailWord_539729).sum := by decide
  have hdescent : baseEnd_539729 < baseStart_539729 := by decide
  rcases family_descends (prefixWord ++ tailWord_539729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539742 : List Nat := [4, 4, 1, 1, 1, 1, 1, 7]
def baseStart_539742 : Nat := 118140960795 + 539742 * 2 ^ 59
def prefixEnd_539742 : Nat := 4983230072969 + 3 ^ 40 * 539742 * 2
def baseEnd_539742 : Nat := 82117651976039256486749

theorem tailTrace_539742 : CollatzResearch.WordTrace tailWord_539742 prefixEnd_539742 82117651976039256486749 := by
  unfold tailWord_539742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2460751001326798679979685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13124005340409592959891653 2460751001326798679979685)
  ·
    refine ⟨461390812748774752496191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2460751001326798679979685 461390812748774752496191)
    ·
      refine ⟨692086219123162128744287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 461390812748774752496191 692086219123162128744287)
      ·
        refine ⟨1038129328684743193116431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692086219123162128744287 1038129328684743193116431)
        ·
          refine ⟨1557193993027114789674647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1038129328684743193116431 1557193993027114789674647)
          ·
            refine ⟨2335790989540672184511971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557193993027114789674647 2335790989540672184511971)
            ·
              refine ⟨3503686484311008276767957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335790989540672184511971 3503686484311008276767957)
              ·
                refine ⟨82117651976039256486749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3503686484311008276767957 82117651976039256486749)
                ·
                  rfl

theorem cell20_539742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_539742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539742 prefixEnd_539742 := by exact prefixLift 539742
  have htrace : WordTrace (prefixWord ++ tailWord_539742) baseStart_539742 baseEnd_539742 := by
    simpa [prefixWord, tailWord_539742, baseEnd_539742] using wordTrace_append hprefix tailTrace_539742
  have hstable : (prefixWord ++ tailWord_539742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539742).length < 2 ^ (prefixWord ++ tailWord_539742).sum := by decide
  have hdescent : baseEnd_539742 < baseStart_539742 := by decide
  rcases family_descends (prefixWord ++ tailWord_539742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539760 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_539760 : Nat := 118140960795 + 539760 * 2 ^ 59
def prefixEnd_539760 : Nat := 4983230072969 + 3 ^ 40 * 539760 * 2
def baseEnd_539760 : Nat := 246361171618589706860173

theorem tailTrace_539760 : CollatzResearch.WordTrace tailWord_539760 prefixEnd_539760 246361171618589706860173 := by
  unfold tailWord_539760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9843332262274589256996367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13124443016366119009328489 9843332262274589256996367)
  ·
    refine ⟨14764998393411883885494551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9843332262274589256996367 14764998393411883885494551)
    ·
      refine ⟨22147497590117825828241827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14764998393411883885494551 22147497590117825828241827)
      ·
        refine ⟨33221246385176738742362741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22147497590117825828241827 33221246385176738742362741)
        ·
          refine ⟨3114491848610319257096507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33221246385176738742362741 3114491848610319257096507)
          ·
            refine ⟨4671737772915478885644761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3114491848610319257096507 4671737772915478885644761)
            ·
              refine ⟨3503803329686609164233571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4671737772915478885644761 3503803329686609164233571)
              ·
                refine ⟨5255704994529913746350357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3503803329686609164233571 5255704994529913746350357)
                ·
                  refine ⟨246361171618589706860173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5255704994529913746350357 246361171618589706860173)
                  ·
                    rfl

theorem cell20_539760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_539760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539760 prefixEnd_539760 := by exact prefixLift 539760
  have htrace : WordTrace (prefixWord ++ tailWord_539760) baseStart_539760 baseEnd_539760 := by
    simpa [prefixWord, tailWord_539760, baseEnd_539760] using wordTrace_append hprefix tailTrace_539760
  have hstable : (prefixWord ++ tailWord_539760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539760).length < 2 ^ (prefixWord ++ tailWord_539760).sum := by decide
  have hdescent : baseEnd_539760 < baseStart_539760 := by decide
  rcases family_descends (prefixWord ++ tailWord_539760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539767 : List Nat := [1, 1, 3, 1, 1, 4, 1, 8]
def baseStart_539767 : Nat := 118140960795 + 539767 * 2 ^ 59
def prefixEnd_539767 : Nat := 4983230072969 + 3 ^ 40 * 539767 * 2
def baseEnd_539767 : Nat := 82121455536442931208937

theorem tailTrace_539767 : CollatzResearch.WordTrace tailWord_539767 prefixEnd_539767 82121455536442931208937 := by
  unfold tailWord_539767
  simp only [CollatzResearch.WordTrace]
  refine ⟨19686919835523818709497555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13124613223682545806331703 19686919835523818709497555)
  ·
    refine ⟨29530379753285728064246333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19686919835523818709497555 29530379753285728064246333)
    ·
      refine ⟨11073892407482148024092375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29530379753285728064246333 11073892407482148024092375)
      ·
        refine ⟨16610838611223222036138563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11073892407482148024092375 16610838611223222036138563)
        ·
          refine ⟨24916257916834833054207845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16610838611223222036138563 24916257916834833054207845)
          ·
            refine ⟨4671798359406531197663971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24916257916834833054207845 4671798359406531197663971)
            ·
              refine ⟨7007697539109796796495957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4671798359406531197663971 7007697539109796796495957)
              ·
                refine ⟨82121455536442931208937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7007697539109796796495957 82121455536442931208937)
                ·
                  rfl

theorem cell20_539767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 8].length) (baseStart_539767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539767 prefixEnd_539767 := by exact prefixLift 539767
  have htrace : WordTrace (prefixWord ++ tailWord_539767) baseStart_539767 baseEnd_539767 := by
    simpa [prefixWord, tailWord_539767, baseEnd_539767] using wordTrace_append hprefix tailTrace_539767
  have hstable : (prefixWord ++ tailWord_539767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539767).length < 2 ^ (prefixWord ++ tailWord_539767).sum := by decide
  have hdescent : baseEnd_539767 < baseStart_539767 := by decide
  rcases family_descends (prefixWord ++ tailWord_539767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539784 : List Nat := [2, 1, 3, 4, 2, 8]
def baseStart_539784 : Nat := 118140960795 + 539784 * 2 ^ 59
def prefixEnd_539784 : Nat := 4983230072969 + 3 ^ 40 * 539784 * 2
def baseEnd_539784 : Nat := 9124893550835270002225

theorem tailTrace_539784 : CollatzResearch.WordTrace tailWord_539784 prefixEnd_539784 9124893550835270002225 := by
  unfold tailWord_539784
  simp only [CollatzResearch.WordTrace]
  refine ⟨9843769938231115306433203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13125026584308153741910937 9843769938231115306433203)
  ·
    refine ⟨14765654907346672959649805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9843769938231115306433203 14765654907346672959649805)
    ·
      refine ⟨5537120590255002359868677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14765654907346672959649805 5537120590255002359868677)
      ·
        refine ⟨1038210110672812942475377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5537120590255002359868677 1038210110672812942475377)
        ·
          refine ⟨778657583004609706856533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1038210110672812942475377 778657583004609706856533)
          ·
            refine ⟨9124893550835270002225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 778657583004609706856533 9124893550835270002225)
            ·
              rfl

theorem cell20_539784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 8].length) (baseStart_539784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539784 prefixEnd_539784 := by exact prefixLift 539784
  have htrace : WordTrace (prefixWord ++ tailWord_539784) baseStart_539784 baseEnd_539784 := by
    simpa [prefixWord, tailWord_539784, baseEnd_539784] using wordTrace_append hprefix tailTrace_539784
  have hstable : (prefixWord ++ tailWord_539784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539784).length < 2 ^ (prefixWord ++ tailWord_539784).sum := by decide
  have hdescent : baseEnd_539784 < baseStart_539784 := by decide
  rcases family_descends (prefixWord ++ tailWord_539784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539790 : List Nat := [4, 1, 1, 3, 2, 3, 2, 2, 2]
def baseStart_539790 : Nat := 118140960795 + 539790 * 2 ^ 59
def prefixEnd_539790 : Nat := 4983230072969 + 3 ^ 40 * 539790 * 2
def baseEnd_539790 : Nat := 246374864436042935860051

theorem tailTrace_539790 : CollatzResearch.WordTrace tailWord_539790 prefixEnd_539790 246374864436042935860051 := by
  unfold tailWord_539790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2460969839305061704698103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13125172476293662425056549 2460969839305061704698103)
  ·
    refine ⟨3691454758957592557047155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2460969839305061704698103 3691454758957592557047155)
    ·
      refine ⟨5537182138436388835570733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3691454758957592557047155 5537182138436388835570733)
      ·
        refine ⟨2076443301913645813339025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5537182138436388835570733 2076443301913645813339025)
        ·
          refine ⟨1557332476435234360004269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2076443301913645813339025 1557332476435234360004269)
          ·
            refine ⟨583999678663212885001601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1557332476435234360004269 583999678663212885001601)
            ·
              refine ⟨437999758997409663751201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 583999678663212885001601 437999758997409663751201)
              ·
                refine ⟨328499819248057247813401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437999758997409663751201 328499819248057247813401)
                ·
                  refine ⟨246374864436042935860051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328499819248057247813401 246374864436042935860051)
                  ·
                    rfl

theorem cell20_539790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_539790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539790 prefixEnd_539790 := by exact prefixLift 539790
  have htrace : WordTrace (prefixWord ++ tailWord_539790) baseStart_539790 baseEnd_539790 := by
    simpa [prefixWord, tailWord_539790, baseEnd_539790] using wordTrace_append hprefix tailTrace_539790
  have hstable : (prefixWord ++ tailWord_539790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539790).length < 2 ^ (prefixWord ++ tailWord_539790).sum := by decide
  have hdescent : baseEnd_539790 < baseStart_539790 := by decide
  rcases family_descends (prefixWord ++ tailWord_539790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539815 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 6]
def baseStart_539815 : Nat := 118140960795 + 539815 * 2 ^ 59
def prefixEnd_539815 : Nat := 4983230072969 + 3 ^ 40 * 539815 * 2
def baseEnd_539815 : Nat := 246386275117253960026615

theorem tailTrace_539815 : CollatzResearch.WordTrace tailWord_539815 prefixEnd_539815 246386275117253960026615 := by
  unfold tailWord_539815
  simp only [CollatzResearch.WordTrace]
  refine ⟨19688670539349922907244899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13125780359566615271496599 19688670539349922907244899)
  ·
    refine ⟨29533005809024884360867349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19688670539349922907244899 29533005809024884360867349)
    ·
      refine ⟨1384359647298041454415657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29533005809024884360867349 1384359647298041454415657)
      ·
        refine ⟨1038269735473531090811743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1384359647298041454415657 1038269735473531090811743)
        ·
          refine ⟨1557404603210296636217615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1038269735473531090811743 1557404603210296636217615)
          ·
            refine ⟨2336106904815444954326423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1557404603210296636217615 2336106904815444954326423)
            ·
              refine ⟨3504160357223167431489635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2336106904815444954326423 3504160357223167431489635)
              ·
                refine ⟨5256240535834751147234453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3504160357223167431489635 5256240535834751147234453)
                ·
                  refine ⟨246386275117253960026615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5256240535834751147234453 246386275117253960026615)
                  ·
                    rfl

theorem cell20_539815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_539815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539815 prefixEnd_539815 := by exact prefixLift 539815
  have htrace : WordTrace (prefixWord ++ tailWord_539815) baseStart_539815 baseEnd_539815 := by
    simpa [prefixWord, tailWord_539815, baseEnd_539815] using wordTrace_append hprefix tailTrace_539815
  have hstable : (prefixWord ++ tailWord_539815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539815).length < 2 ^ (prefixWord ++ tailWord_539815).sum := by decide
  have hdescent : baseEnd_539815 < baseStart_539815 := by decide
  rcases family_descends (prefixWord ++ tailWord_539815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539818 : List Nat := [3, 1, 5, 1, 1, 2, 3, 4]
def baseStart_539818 : Nat := 118140960795 + 539818 * 2 ^ 59
def prefixEnd_539818 : Nat := 4983230072969 + 3 ^ 40 * 539818 * 2
def baseEnd_539818 : Nat := 82129214799666427642201

theorem tailTrace_539818 : CollatzResearch.WordTrace tailWord_539818 prefixEnd_539818 82129214799666427642201 := by
  unfold tailWord_539818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4922194989584763604901027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13125853305559369613069405 4922194989584763604901027)
  ·
    refine ⟨7383292484377145407351541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4922194989584763604901027 7383292484377145407351541)
    ·
      refine ⟨692183670410357381939207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7383292484377145407351541 692183670410357381939207)
      ·
        refine ⟨1038275505615536072908811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692183670410357381939207 1038275505615536072908811)
        ·
          refine ⟨1557413258423304109363217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1038275505615536072908811 1557413258423304109363217)
          ·
            refine ⟨1168059943817478082022413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1557413258423304109363217 1168059943817478082022413)
            ·
              refine ⟨438022478931554280758405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1168059943817478082022413 438022478931554280758405)
              ·
                refine ⟨82129214799666427642201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 438022478931554280758405 82129214799666427642201)
                ·
                  rfl

theorem cell20_539818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_539818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539818 prefixEnd_539818 := by exact prefixLift 539818
  have htrace : WordTrace (prefixWord ++ tailWord_539818) baseStart_539818 baseEnd_539818 := by
    simpa [prefixWord, tailWord_539818, baseEnd_539818] using wordTrace_append hprefix tailTrace_539818
  have hstable : (prefixWord ++ tailWord_539818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539818).length < 2 ^ (prefixWord ++ tailWord_539818).sum := by decide
  have hdescent : baseEnd_539818 < baseStart_539818 := by decide
  rcases family_descends (prefixWord ++ tailWord_539818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539842 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 5]
def baseStart_539842 : Nat := 118140960795 + 539842 * 2 ^ 59
def prefixEnd_539842 : Nat := 4983230072969 + 3 ^ 40 * 539842 * 2
def baseEnd_539842 : Nat := 246398598652961866126505

theorem tailTrace_539842 : CollatzResearch.WordTrace tailWord_539842 prefixEnd_539842 246398598652961866126505 := by
  unfold tailWord_539842
  simp only [CollatzResearch.WordTrace]
  refine ⟨4922413827563026629619445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13126436873501404345651853 4922413827563026629619445)
  ·
    refine ⟨461476296334033746526823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4922413827563026629619445 461476296334033746526823)
    ·
      refine ⟨692214444501050619790235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 461476296334033746526823 692214444501050619790235)
      ·
        refine ⟨1038321666751575929685353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 692214444501050619790235 1038321666751575929685353)
        ·
          refine ⟨778741250063681947264015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1038321666751575929685353 778741250063681947264015)
          ·
            refine ⟨1168111875095522920896023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778741250063681947264015 1168111875095522920896023)
            ·
              refine ⟨1752167812643284381344035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168111875095522920896023 1752167812643284381344035)
              ·
                refine ⟨2628251718964926572016053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752167812643284381344035 2628251718964926572016053)
                ·
                  refine ⟨246398598652961866126505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2628251718964926572016053 246398598652961866126505)
                  ·
                    rfl

theorem cell20_539842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_539842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539842 prefixEnd_539842 := by exact prefixLift 539842
  have htrace : WordTrace (prefixWord ++ tailWord_539842) baseStart_539842 baseEnd_539842 := by
    simpa [prefixWord, tailWord_539842, baseEnd_539842] using wordTrace_append hprefix tailTrace_539842
  have hstable : (prefixWord ++ tailWord_539842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539842).length < 2 ^ (prefixWord ++ tailWord_539842).sum := by decide
  have hdescent : baseEnd_539842 < baseStart_539842 := by decide
  rcases family_descends (prefixWord ++ tailWord_539842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539887 : List Nat := [1, 1, 2, 1, 7, 2, 1, 3, 2]
def baseStart_539887 : Nat := 118140960795 + 539887 * 2 ^ 59
def prefixEnd_539887 : Nat := 4983230072969 + 3 ^ 40 * 539887 * 2
def baseEnd_539887 : Nat := 246419137879141709626321

theorem tailTrace_539887 : CollatzResearch.WordTrace tailWord_539887 prefixEnd_539887 246419137879141709626321 := by
  unfold tailWord_539887
  simp only [CollatzResearch.WordTrace]
  refine ⟨19691296595089079203865915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13127531063392719469243943 19691296595089079203865915)
  ·
    refine ⟨29536944892633618805798873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19691296595089079203865915 29536944892633618805798873)
    ·
      refine ⟨22152708669475214104349155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29536944892633618805798873 22152708669475214104349155)
      ·
        refine ⟨33229063004212821156523733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22152708669475214104349155 33229063004212821156523733)
        ·
          refine ⟨778806164161237995856025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 33229063004212821156523733 778806164161237995856025)
          ·
            refine ⟨584104623120928496892019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 778806164161237995856025 584104623120928496892019)
            ·
              refine ⟨876156934681392745338029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584104623120928496892019 876156934681392745338029)
              ·
                refine ⟨328558850505522279501761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 876156934681392745338029 328558850505522279501761)
                ·
                  refine ⟨246419137879141709626321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328558850505522279501761 246419137879141709626321)
                  ·
                    rfl

theorem cell20_539887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 2].length) (baseStart_539887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539887 prefixEnd_539887 := by exact prefixLift 539887
  have htrace : WordTrace (prefixWord ++ tailWord_539887) baseStart_539887 baseEnd_539887 := by
    simpa [prefixWord, tailWord_539887, baseEnd_539887] using wordTrace_append hprefix tailTrace_539887
  have hstable : (prefixWord ++ tailWord_539887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539887).length < 2 ^ (prefixWord ++ tailWord_539887).sum := by decide
  have hdescent : baseEnd_539887 < baseStart_539887 := by decide
  rcases family_descends (prefixWord ++ tailWord_539887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539905 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 5]
def baseStart_539905 : Nat := 118140960795 + 539905 * 2 ^ 59
def prefixEnd_539905 : Nat := 4983230072969 + 3 ^ 40 * 539905 * 2
def baseEnd_539905 : Nat := 246427353569613647026247

theorem tailTrace_539905 : CollatzResearch.WordTrace tailWord_539905 prefixEnd_539905 246427353569613647026247 := by
  unfold tailWord_539905
  simp only [CollatzResearch.WordTrace]
  refine ⟨19691953109023868278021169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13127968739349245518680779 19691953109023868278021169)
  ·
    refine ⟨14768964831767901208515877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19691953109023868278021169 14768964831767901208515877)
    ·
      refine ⟨2769180905956481476596727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14768964831767901208515877 2769180905956481476596727)
      ·
        refine ⟨4153771358934722214895091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2769180905956481476596727 4153771358934722214895091)
        ·
          refine ⟨6230657038402083322342637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4153771358934722214895091 6230657038402083322342637)
          ·
            refine ⟨2336496389400781245878489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6230657038402083322342637 2336496389400781245878489)
            ·
              refine ⟨1752372292050585934408867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2336496389400781245878489 1752372292050585934408867)
              ·
                refine ⟨2628558438075878901613301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1752372292050585934408867 2628558438075878901613301)
                ·
                  refine ⟨246427353569613647026247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2628558438075878901613301 246427353569613647026247)
                  ·
                    rfl

theorem cell20_539905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_539905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539905 prefixEnd_539905 := by exact prefixLift 539905
  have htrace : WordTrace (prefixWord ++ tailWord_539905) baseStart_539905 baseEnd_539905 := by
    simpa [prefixWord, tailWord_539905, baseEnd_539905] using wordTrace_append hprefix tailTrace_539905
  have hstable : (prefixWord ++ tailWord_539905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539905).length < 2 ^ (prefixWord ++ tailWord_539905).sum := by decide
  have hdescent : baseEnd_539905 < baseStart_539905 := by decide
  rcases family_descends (prefixWord ++ tailWord_539905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539908 : List Nat := [2, 3, 2, 2, 2, 3, 1, 1, 4]
def baseStart_539908 : Nat := 118140960795 + 539908 * 2 ^ 59
def prefixEnd_539908 : Nat := 4983230072969 + 3 ^ 40 * 539908 * 2
def baseEnd_539908 : Nat := 246428722851358969926235

theorem tailTrace_539908 : CollatzResearch.WordTrace tailWord_539908 prefixEnd_539908 246428722851358969926235 := by
  unfold tailWord_539908
  simp only [CollatzResearch.WordTrace]
  refine ⟨9846031264006499895190189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13128041685341999860253585 9846031264006499895190189)
  ·
    refine ⟨3692261724002437460696321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9846031264006499895190189 3692261724002437460696321)
    ·
      refine ⟨2769196293001828095522241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3692261724002437460696321 2769196293001828095522241)
      ·
        refine ⟨2076897219751371071641681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2769196293001828095522241 2076897219751371071641681)
        ·
          refine ⟨1557672914813528303731261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2076897219751371071641681 1557672914813528303731261)
          ·
            refine ⟨584127343055073113899223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1557672914813528303731261 584127343055073113899223)
            ·
              refine ⟨876191014582609670848835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584127343055073113899223 876191014582609670848835)
              ·
                refine ⟨1314286521873914506273253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876191014582609670848835 1314286521873914506273253)
                ·
                  refine ⟨246428722851358969926235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1314286521873914506273253 246428722851358969926235)
                  ·
                    rfl

theorem cell20_539908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_539908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539908 prefixEnd_539908 := by exact prefixLift 539908
  have htrace : WordTrace (prefixWord ++ tailWord_539908) baseStart_539908 baseEnd_539908 := by
    simpa [prefixWord, tailWord_539908, baseEnd_539908] using wordTrace_append hprefix tailTrace_539908
  have hstable : (prefixWord ++ tailWord_539908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539908).length < 2 ^ (prefixWord ++ tailWord_539908).sum := by decide
  have hdescent : baseEnd_539908 < baseStart_539908 := by decide
  rcases family_descends (prefixWord ++ tailWord_539908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539957 : List Nat := [1, 3, 3, 1, 2, 10]
def baseStart_539957 : Nat := 118140960795 + 539957 * 2 ^ 59
def prefixEnd_539957 : Nat := 4983230072969 + 3 ^ 40 * 539957 * 2
def baseEnd_539957 : Nat := 9127818066167873233063

theorem tailTrace_539957 : CollatzResearch.WordTrace tailWord_539957 prefixEnd_539957 9127818066167873233063 := by
  unfold tailWord_539957
  simp only [CollatzResearch.WordTrace]
  refine ⟨19693849704835481158914125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13129233136556987439276083 19693849704835481158914125)
  ·
    refine ⟨7385193639313305434592797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19693849704835481158914125 7385193639313305434592797)
    ·
      refine ⟨2769447614742489537972299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7385193639313305434592797 2769447614742489537972299)
      ·
        refine ⟨4154171422113734306958449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2769447614742489537972299 4154171422113734306958449)
        ·
          refine ⟨3115628566585300730218837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4154171422113734306958449 3115628566585300730218837)
          ·
            refine ⟨9127818066167873233063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3115628566585300730218837 9127818066167873233063)
            ·
              rfl

theorem cell20_539957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 10].length) (baseStart_539957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539957 prefixEnd_539957 := by exact prefixLift 539957
  have htrace : WordTrace (prefixWord ++ tailWord_539957) baseStart_539957 baseEnd_539957 := by
    simpa [prefixWord, tailWord_539957, baseEnd_539957] using wordTrace_append hprefix tailTrace_539957
  have hstable : (prefixWord ++ tailWord_539957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539957).length < 2 ^ (prefixWord ++ tailWord_539957).sum := by decide
  have hdescent : baseEnd_539957 < baseStart_539957 := by decide
  rcases family_descends (prefixWord ++ tailWord_539957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_539997 : List Nat := [1, 4, 5, 1, 1, 1, 2, 3, 2]
def baseStart_539997 : Nat := 118140960795 + 539997 * 2 ^ 59
def prefixEnd_539997 : Nat := 4983230072969 + 3 ^ 40 * 539997 * 2
def baseEnd_539997 : Nat := 246469344876470215959205

theorem tailTrace_539997 : CollatzResearch.WordTrace tailWord_539997 prefixEnd_539997 246469344876470215959205 := by
  unfold tailWord_539997
  simp only [CollatzResearch.WordTrace]
  refine ⟨19695308624690567990370245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13130205749793711993580163 19695308624690567990370245)
  ·
    refine ⟨3692870367129481498194421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19695308624690567990370245 3692870367129481498194421)
    ·
      refine ⟨346206596918388890455727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3692870367129481498194421 346206596918388890455727)
      ·
        refine ⟨519309895377583335683591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346206596918388890455727 519309895377583335683591)
        ·
          refine ⟨778964843066375003525387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519309895377583335683591 778964843066375003525387)
          ·
            refine ⟨1168447264599562505288081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778964843066375003525387 1168447264599562505288081)
            ·
              refine ⟨876335448449671878966061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1168447264599562505288081 876335448449671878966061)
              ·
                refine ⟨328625793168626954612273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 876335448449671878966061 328625793168626954612273)
                ·
                  refine ⟨246469344876470215959205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328625793168626954612273 246469344876470215959205)
                  ·
                    rfl

theorem cell20_539997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_539997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_539997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_539997 prefixEnd_539997 := by exact prefixLift 539997
  have htrace : WordTrace (prefixWord ++ tailWord_539997) baseStart_539997 baseEnd_539997 := by
    simpa [prefixWord, tailWord_539997, baseEnd_539997] using wordTrace_append hprefix tailTrace_539997
  have hstable : (prefixWord ++ tailWord_539997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_539997).length < 2 ^ (prefixWord ++ tailWord_539997).sum := by decide
  have hdescent : baseEnd_539997 < baseStart_539997 := by decide
  rcases family_descends (prefixWord ++ tailWord_539997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540046 : List Nat := [4, 1, 1, 4, 2, 2, 2, 4]
def baseStart_540046 : Nat := 118140960795 + 540046 * 2 ^ 59
def prefixEnd_540046 : Nat := 4983230072969 + 3 ^ 40 * 540046 * 2
def baseEnd_540046 : Nat := 82163903270547941108557

theorem tailTrace_540046 : CollatzResearch.WordTrace tailWord_540046 prefixEnd_540046 82163903270547941108557 := by
  unfold tailWord_540046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2462136975189131169862999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13131397201008699572602661 2462136975189131169862999)
  ·
    refine ⟨3693205462783696754794499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2462136975189131169862999 3693205462783696754794499)
    ·
      refine ⟨5539808194175545132191749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3693205462783696754794499 5539808194175545132191749)
      ·
        refine ⟨1038714036407914712285953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5539808194175545132191749 1038714036407914712285953)
        ·
          refine ⟨779035527305936034214465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1038714036407914712285953 779035527305936034214465)
          ·
            refine ⟨584276645479452025660849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 779035527305936034214465 584276645479452025660849)
            ·
              refine ⟨438207484109589019245637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584276645479452025660849 438207484109589019245637)
              ·
                refine ⟨82163903270547941108557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 438207484109589019245637 82163903270547941108557)
                ·
                  rfl

theorem cell20_540046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_540046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540046 prefixEnd_540046 := by exact prefixLift 540046
  have htrace : WordTrace (prefixWord ++ tailWord_540046) baseStart_540046 baseEnd_540046 := by
    simpa [prefixWord, tailWord_540046, baseEnd_540046] using wordTrace_append hprefix tailTrace_540046
  have hstable : (prefixWord ++ tailWord_540046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540046).length < 2 ^ (prefixWord ++ tailWord_540046).sum := by decide
  have hdescent : baseEnd_540046 < baseStart_540046 := by decide
  rcases family_descends (prefixWord ++ tailWord_540046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540056 : List Nat := [2, 1, 2, 5, 3, 1, 1, 3, 2]
def baseStart_540056 : Nat := 118140960795 + 540056 * 2 ^ 59
def prefixEnd_540056 : Nat := 4983230072969 + 3 ^ 40 * 540056 * 2
def baseEnd_540056 : Nat := 246496274084128232992297

theorem tailTrace_540056 : CollatzResearch.WordTrace tailWord_540056 prefixEnd_540056 246496274084128232992297 := by
  unfold tailWord_540056
  simp only [CollatzResearch.WordTrace]
  refine ⟨9848730265738410533384011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13131640354317880711178681 9848730265738410533384011)
  ·
    refine ⟨14773095398607615800076017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9848730265738410533384011 14773095398607615800076017)
    ·
      refine ⟨11079821548955711850057013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14773095398607615800076017 11079821548955711850057013)
      ·
        refine ⟨1038733270214597985942845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11079821548955711850057013 1038733270214597985942845)
        ·
          refine ⟨389524976330474244728567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1038733270214597985942845 389524976330474244728567)
          ·
            refine ⟨584287464495711367092851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389524976330474244728567 584287464495711367092851)
            ·
              refine ⟨876431196743567050639277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584287464495711367092851 876431196743567050639277)
              ·
                refine ⟨328661698778837643989729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 876431196743567050639277 328661698778837643989729)
                ·
                  refine ⟨246496274084128232992297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328661698778837643989729 246496274084128232992297)
                  ·
                    rfl

theorem cell20_540056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 2].length) (baseStart_540056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540056 prefixEnd_540056 := by exact prefixLift 540056
  have htrace : WordTrace (prefixWord ++ tailWord_540056) baseStart_540056 baseEnd_540056 := by
    simpa [prefixWord, tailWord_540056, baseEnd_540056] using wordTrace_append hprefix tailTrace_540056
  have hstable : (prefixWord ++ tailWord_540056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540056).length < 2 ^ (prefixWord ++ tailWord_540056).sum := by decide
  have hdescent : baseEnd_540056 < baseStart_540056 := by decide
  rcases family_descends (prefixWord ++ tailWord_540056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540150 : List Nat := [5, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_540150 : Nat := 118140960795 + 540150 * 2 ^ 59
def prefixEnd_540150 : Nat := 4983230072969 + 3 ^ 40 * 540150 * 2
def baseEnd_540150 : Nat := 246539178245481683858579

theorem tailTrace_540150 : CollatzResearch.WordTrace tailWord_540150 prefixEnd_540150 246539178245481683858579 := by
  unfold tailWord_540150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1231305562071017195043119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13133925995424183413793269 1231305562071017195043119)
  ·
    refine ⟨1846958343106525792564679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1231305562071017195043119 1846958343106525792564679)
    ·
      refine ⟨2770437514659788688847019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1846958343106525792564679 2770437514659788688847019)
      ·
        refine ⟨4155656271989683033270529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2770437514659788688847019 4155656271989683033270529)
        ·
          refine ⟨3116742203992262274952897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4155656271989683033270529 3116742203992262274952897)
          ·
            refine ⟨2337556652994196706214673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3116742203992262274952897 2337556652994196706214673)
            ·
              refine ⟨1753167489745647529661005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2337556652994196706214673 1753167489745647529661005)
              ·
                refine ⟨657437808654617823622877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1753167489745647529661005 657437808654617823622877)
                ·
                  refine ⟨246539178245481683858579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657437808654617823622877 246539178245481683858579)
                  ·
                    rfl

theorem cell20_540150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_540150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540150 prefixEnd_540150 := by exact prefixLift 540150
  have htrace : WordTrace (prefixWord ++ tailWord_540150) baseStart_540150 baseEnd_540150 := by
    simpa [prefixWord, tailWord_540150, baseEnd_540150] using wordTrace_append hprefix tailTrace_540150
  have hstable : (prefixWord ++ tailWord_540150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540150).length < 2 ^ (prefixWord ++ tailWord_540150).sum := by decide
  have hdescent : baseEnd_540150 < baseStart_540150 := by decide
  rcases family_descends (prefixWord ++ tailWord_540150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540195 : List Nat := [1, 1, 1, 4, 5, 1, 2, 1, 4]
def baseStart_540195 : Nat := 118140960795 + 540195 * 2 ^ 59
def prefixEnd_540195 : Nat := 4983230072969 + 3 ^ 40 * 540195 * 2
def baseEnd_540195 : Nat := 246559717471661527358395

theorem tailTrace_540195 : CollatzResearch.WordTrace tailWord_540195 prefixEnd_540195 246559717471661527358395 := by
  unfold tailWord_540195
  simp only [CollatzResearch.WordTrace]
  refine ⟨19702530277973247806078039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13135020185315498537385359 19702530277973247806078039)
  ·
    refine ⟨29553795416959871709117059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19702530277973247806078039 29553795416959871709117059)
    ·
      refine ⟨44330693125439807563675589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29553795416959871709117059 44330693125439807563675589)
      ·
        refine ⟨8312004961019963918189173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44330693125439807563675589 8312004961019963918189173)
        ·
          refine ⟨779250465095621617330235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8312004961019963918189173 779250465095621617330235)
          ·
            refine ⟨1168875697643432425995353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779250465095621617330235 1168875697643432425995353)
            ·
              refine ⟨876656773232574319496515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1168875697643432425995353 876656773232574319496515)
              ·
                refine ⟨1314985159848861479244773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876656773232574319496515 1314985159848861479244773)
                ·
                  refine ⟨246559717471661527358395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1314985159848861479244773 246559717471661527358395)
                  ·
                    rfl

theorem cell20_540195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 4].length) (baseStart_540195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540195 prefixEnd_540195 := by exact prefixLift 540195
  have htrace : WordTrace (prefixWord ++ tailWord_540195) baseStart_540195 baseEnd_540195 := by
    simpa [prefixWord, tailWord_540195, baseEnd_540195] using wordTrace_append hprefix tailTrace_540195
  have hstable : (prefixWord ++ tailWord_540195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540195).length < 2 ^ (prefixWord ++ tailWord_540195).sum := by decide
  have hdescent : baseEnd_540195 < baseStart_540195 := by decide
  rcases family_descends (prefixWord ++ tailWord_540195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540216 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 4]
def baseStart_540216 : Nat := 118140960795 + 540216 * 2 ^ 59
def prefixEnd_540216 : Nat := 4983230072969 + 3 ^ 40 * 540216 * 2
def baseEnd_540216 : Nat := 246569302443878787658309

theorem tailTrace_540216 : CollatzResearch.WordTrace tailWord_540216 prefixEnd_540216 246569302443878787658309 := by
  unfold tailWord_540216
  simp only [CollatzResearch.WordTrace]
  refine ⟨9851648105448584196296251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13135530807264778928395001 9851648105448584196296251)
  ·
    refine ⟨14777472158172876294444377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9851648105448584196296251 14777472158172876294444377)
    ·
      refine ⟨11083104118629657220833283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14777472158172876294444377 11083104118629657220833283)
      ·
        refine ⟨16624656177944485831249925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11083104118629657220833283 16624656177944485831249925)
        ·
          refine ⟨3117123033364591093359361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16624656177944485831249925 3117123033364591093359361)
          ·
            refine ⟨2337842275023443320019521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3117123033364591093359361 2337842275023443320019521)
            ·
              refine ⟨1753381706267582490014641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2337842275023443320019521 1753381706267582490014641)
              ·
                refine ⟨1315036279700686867510981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1753381706267582490014641 1315036279700686867510981)
                ·
                  refine ⟨246569302443878787658309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1315036279700686867510981 246569302443878787658309)
                  ·
                    rfl

theorem cell20_540216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_540216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540216 prefixEnd_540216 := by exact prefixLift 540216
  have htrace : WordTrace (prefixWord ++ tailWord_540216) baseStart_540216 baseEnd_540216 := by
    simpa [prefixWord, tailWord_540216, baseEnd_540216] using wordTrace_append hprefix tailTrace_540216
  have hstable : (prefixWord ++ tailWord_540216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540216).length < 2 ^ (prefixWord ++ tailWord_540216).sum := by decide
  have hdescent : baseEnd_540216 < baseStart_540216 := by decide
  rcases family_descends (prefixWord ++ tailWord_540216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540223 : List Nat := [1, 1, 2, 2, 3, 4, 1, 6]
def baseStart_540223 : Nat := 118140960795 + 540223 * 2 ^ 59
def prefixEnd_540223 : Nat := 4983230072969 + 3 ^ 40 * 540223 * 2
def baseEnd_540223 : Nat := 82190832478205958141649

theorem tailTrace_540223 : CollatzResearch.WordTrace tailWord_540223 prefixEnd_540223 82190832478205958141649 := by
  unfold tailWord_540223
  simp only [CollatzResearch.WordTrace]
  refine ⟨19703551521871808588097323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13135701014581205725398215 19703551521871808588097323)
  ·
    refine ⟨29555327282807712882145985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19703551521871808588097323 29555327282807712882145985)
    ·
      refine ⟨22166495462105784661609489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29555327282807712882145985 22166495462105784661609489)
      ·
        refine ⟨16624871596579338496207117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22166495462105784661609489 16624871596579338496207117)
        ·
          refine ⟨6234326848717251936077669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16624871596579338496207117 6234326848717251936077669)
          ·
            refine ⟨1168936284134484738014563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6234326848717251936077669 1168936284134484738014563)
            ·
              refine ⟨1753404426201727107021845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1168936284134484738014563 1753404426201727107021845)
              ·
                refine ⟨82190832478205958141649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1753404426201727107021845 82190832478205958141649)
                ·
                  rfl

theorem cell20_540223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 6].length) (baseStart_540223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540223 prefixEnd_540223 := by exact prefixLift 540223
  have htrace : WordTrace (prefixWord ++ tailWord_540223) baseStart_540223 baseEnd_540223 := by
    simpa [prefixWord, tailWord_540223, baseEnd_540223] using wordTrace_append hprefix tailTrace_540223
  have hstable : (prefixWord ++ tailWord_540223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540223).length < 2 ^ (prefixWord ++ tailWord_540223).sum := by decide
  have hdescent : baseEnd_540223 < baseStart_540223 := by decide
  rcases family_descends (prefixWord ++ tailWord_540223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540246 : List Nat := [5, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_540246 : Nat := 118140960795 + 540246 * 2 ^ 59
def prefixEnd_540246 : Nat := 4983230072969 + 3 ^ 40 * 540246 * 2
def baseEnd_540246 : Nat := 246582995261332016658187

theorem tailTrace_540246 : CollatzResearch.WordTrace tailWord_540246 prefixEnd_540246 246582995261332016658187 := by
  unfold tailWord_540246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1231524400049280219761537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13136260267192322344123061 1231524400049280219761537)
  ·
    refine ⟨923643300036960164821153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1231524400049280219761537 923643300036960164821153)
    ·
      refine ⟨692732475027720123615865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 923643300036960164821153 692732475027720123615865)
      ·
        refine ⟨519549356270790092711899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 692732475027720123615865 519549356270790092711899)
        ·
          refine ⟨779324034406185139067849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519549356270790092711899 779324034406185139067849)
          ·
            refine ⟨584493025804638854300887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 779324034406185139067849 584493025804638854300887)
            ·
              refine ⟨876739538706958281451331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584493025804638854300887 876739538706958281451331)
              ·
                refine ⟨1315109308060437422176997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 876739538706958281451331 1315109308060437422176997)
                ·
                  refine ⟨246582995261332016658187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1315109308060437422176997 246582995261332016658187)
                  ·
                    rfl

theorem cell20_540246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_540246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540246 prefixEnd_540246 := by exact prefixLift 540246
  have htrace : WordTrace (prefixWord ++ tailWord_540246) baseStart_540246 baseEnd_540246 := by
    simpa [prefixWord, tailWord_540246, baseEnd_540246] using wordTrace_append hprefix tailTrace_540246
  have hstable : (prefixWord ++ tailWord_540246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540246).length < 2 ^ (prefixWord ++ tailWord_540246).sum := by decide
  have hdescent : baseEnd_540246 < baseStart_540246 := by decide
  rcases family_descends (prefixWord ++ tailWord_540246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540261 : List Nat := [1, 3, 1, 3, 3, 1, 1, 7]
def baseStart_540261 : Nat := 118140960795 + 540261 * 2 ^ 59
def prefixEnd_540261 : Nat := 4983230072969 + 3 ^ 40 * 540261 * 2
def baseEnd_540261 : Nat := 82196613890019543719375

theorem tailTrace_540261 : CollatzResearch.WordTrace tailWord_540261 prefixEnd_540261 82196613890019543719375 := by
  unfold tailWord_540261
  simp only [CollatzResearch.WordTrace]
  refine ⟨19704937495734141077980637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13136624997156094051987091 19704937495734141077980637)
  ·
    refine ⟨7389351560900302904242739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19704937495734141077980637 7389351560900302904242739)
    ·
      refine ⟨11084027341350454356364109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7389351560900302904242739 11084027341350454356364109)
      ·
        refine ⟨4156510253006420383636541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11084027341350454356364109 4156510253006420383636541)
        ·
          refine ⟨1558691344877407643863703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4156510253006420383636541 1558691344877407643863703)
          ·
            refine ⟨2338037017316111465795555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558691344877407643863703 2338037017316111465795555)
            ·
              refine ⟨3507055525974167198693333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2338037017316111465795555 3507055525974167198693333)
              ·
                refine ⟨82196613890019543719375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3507055525974167198693333 82196613890019543719375)
                ·
                  rfl

theorem cell20_540261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 7].length) (baseStart_540261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540261 prefixEnd_540261 := by exact prefixLift 540261
  have htrace : WordTrace (prefixWord ++ tailWord_540261) baseStart_540261 baseEnd_540261 := by
    simpa [prefixWord, tailWord_540261, baseEnd_540261] using wordTrace_append hprefix tailTrace_540261
  have hstable : (prefixWord ++ tailWord_540261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540261).length < 2 ^ (prefixWord ++ tailWord_540261).sum := by decide
  have hdescent : baseEnd_540261 < baseStart_540261 := by decide
  rcases family_descends (prefixWord ++ tailWord_540261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540264 : List Nat := [2, 1, 4, 3, 1, 2, 1, 3, 3]
def baseStart_540264 : Nat := 118140960795 + 540264 * 2 ^ 59
def prefixEnd_540264 : Nat := 4983230072969 + 3 ^ 40 * 540264 * 2
def baseEnd_540264 : Nat := 246591210951803954058113

theorem tailTrace_540264 : CollatzResearch.WordTrace tailWord_540264 prefixEnd_540264 246591210951803954058113 := by
  unfold tailWord_540264
  simp only [CollatzResearch.WordTrace]
  refine ⟨9852523457361636295169923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13136697943148848393559897 9852523457361636295169923)
  ·
    refine ⟨14778785186042454442754885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9852523457361636295169923 14778785186042454442754885)
    ·
      refine ⟨2771022222382960208016541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14778785186042454442754885 2771022222382960208016541)
      ·
        refine ⟨1039133333393610078006203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2771022222382960208016541 1039133333393610078006203)
        ·
          refine ⟨1558700000090415117009305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1039133333393610078006203 1558700000090415117009305)
          ·
            refine ⟨1169025000067811337756979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1558700000090415117009305 1169025000067811337756979)
            ·
              refine ⟨1753537500101717006635469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1169025000067811337756979 1753537500101717006635469)
              ·
                refine ⟨657576562538143877488301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1753537500101717006635469 657576562538143877488301)
                ·
                  refine ⟨246591210951803954058113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657576562538143877488301 246591210951803954058113)
                  ·
                    rfl

theorem cell20_540264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_540264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540264 prefixEnd_540264 := by exact prefixLift 540264
  have htrace : WordTrace (prefixWord ++ tailWord_540264) baseStart_540264 baseEnd_540264 := by
    simpa [prefixWord, tailWord_540264, baseEnd_540264] using wordTrace_append hprefix tailTrace_540264
  have hstable : (prefixWord ++ tailWord_540264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540264).length < 2 ^ (prefixWord ++ tailWord_540264).sum := by decide
  have hdescent : baseEnd_540264 < baseStart_540264 := by decide
  rcases family_descends (prefixWord ++ tailWord_540264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540278 : List Nat := [5, 1, 1, 2, 2, 1, 2, 6]
def baseStart_540278 : Nat := 118140960795 + 540278 * 2 ^ 59
def prefixEnd_540278 : Nat := 4983230072969 + 3 ^ 40 * 540278 * 2
def baseEnd_540278 : Nat := 82199200311094042530463

theorem tailTrace_540278 : CollatzResearch.WordTrace tailWord_540278 prefixEnd_540278 82199200311094042530463 := by
  unfold tailWord_540278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1231597346042034561334343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13137038357781701987566325 1231597346042034561334343)
  ·
    refine ⟨1847396019063051842001515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1231597346042034561334343 1847396019063051842001515)
    ·
      refine ⟨2771094028594577763002273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1847396019063051842001515 2771094028594577763002273)
      ·
        refine ⟨2078320521445933322251705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2771094028594577763002273 2078320521445933322251705)
        ·
          refine ⟨1558740391084449991688779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2078320521445933322251705 1558740391084449991688779)
          ·
            refine ⟨2338110586626674987533169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1558740391084449991688779 2338110586626674987533169)
            ·
              refine ⟨1753582939970006240649877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2338110586626674987533169 1753582939970006240649877)
              ·
                refine ⟨82199200311094042530463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1753582939970006240649877 82199200311094042530463)
                ·
                  rfl

theorem cell20_540278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_540278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540278 prefixEnd_540278 := by exact prefixLift 540278
  have htrace : WordTrace (prefixWord ++ tailWord_540278) baseStart_540278 baseEnd_540278 := by
    simpa [prefixWord, tailWord_540278, baseEnd_540278] using wordTrace_append hprefix tailTrace_540278
  have hstable : (prefixWord ++ tailWord_540278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540278).length < 2 ^ (prefixWord ++ tailWord_540278).sum := by decide
  have hdescent : baseEnd_540278 < baseStart_540278 := by decide
  rcases family_descends (prefixWord ++ tailWord_540278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540302 : List Nat := [4, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_540302 : Nat := 118140960795 + 540302 * 2 ^ 59
def prefixEnd_540302 : Nat := 4983230072969 + 3 ^ 40 * 540302 * 2
def baseEnd_540302 : Nat := 246608555187244710791291

theorem tailTrace_540302 : CollatzResearch.WordTrace tailWord_540302 prefixEnd_540302 246608555187244710791291 := by
  unfold tailWord_540302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2463304111073200635027895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13137621925723736720148773 2463304111073200635027895)
  ·
    refine ⟨3694956166609800952541843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2463304111073200635027895 3694956166609800952541843)
    ·
      refine ⟨5542434249914701428812765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3694956166609800952541843 5542434249914701428812765)
      ·
        refine ⟨2078412843718013035804787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5542434249914701428812765 2078412843718013035804787)
        ·
          refine ⟨3117619265577019553707181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2078412843718013035804787 3117619265577019553707181)
          ·
            refine ⟨1169107224591382332640193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3117619265577019553707181 1169107224591382332640193)
            ·
              refine ⟨876830418443536749480145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169107224591382332640193 876830418443536749480145)
              ·
                refine ⟨657622813832652562110109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 876830418443536749480145 657622813832652562110109)
                ·
                  refine ⟨246608555187244710791291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657622813832652562110109 246608555187244710791291)
                  ·
                    rfl

theorem cell20_540302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_540302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540302 prefixEnd_540302 := by exact prefixLift 540302
  have htrace : WordTrace (prefixWord ++ tailWord_540302) baseStart_540302 baseEnd_540302 := by
    simpa [prefixWord, tailWord_540302, baseEnd_540302] using wordTrace_append hprefix tailTrace_540302
  have hstable : (prefixWord ++ tailWord_540302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540302).length < 2 ^ (prefixWord ++ tailWord_540302).sum := by decide
  have hdescent : baseEnd_540302 < baseStart_540302 := by decide
  rcases family_descends (prefixWord ++ tailWord_540302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540351 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 6]
def baseStart_540351 : Nat := 118140960795 + 540351 * 2 ^ 59
def prefixEnd_540351 : Nat := 4983230072969 + 3 ^ 40 * 540351 * 2
def baseEnd_540351 : Nat := 246630920122418318157757

theorem tailTrace_540351 : CollatzResearch.WordTrace tailWord_540351 prefixEnd_540351 246630920122418318157757 := by
  unfold tailWord_540351
  simp only [CollatzResearch.WordTrace]
  refine ⟨19708220065408086448756907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13138813376938724299171271 19708220065408086448756907)
  ·
    refine ⟨29562330098112129673135361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19708220065408086448756907 29562330098112129673135361)
    ·
      refine ⟨22171747573584097254851521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29562330098112129673135361 22171747573584097254851521)
      ·
        refine ⟨16628810680188072941138641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22171747573584097254851521 16628810680188072941138641)
        ·
          refine ⟨12471608010141054705853981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16628810680188072941138641 12471608010141054705853981)
          ·
            refine ⟨4676853003802895514695243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12471608010141054705853981 4676853003802895514695243)
            ·
              refine ⟨7015279505704343272042865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4676853003802895514695243 7015279505704343272042865)
              ·
                refine ⟨5261459629278257454032149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7015279505704343272042865 5261459629278257454032149)
                ·
                  refine ⟨246630920122418318157757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5261459629278257454032149 246630920122418318157757)
                  ·
                    rfl

theorem cell20_540351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_540351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540351 prefixEnd_540351 := by exact prefixLift 540351
  have htrace : WordTrace (prefixWord ++ tailWord_540351) baseStart_540351 baseEnd_540351 := by
    simpa [prefixWord, tailWord_540351, baseEnd_540351] using wordTrace_append hprefix tailTrace_540351
  have hstable : (prefixWord ++ tailWord_540351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540351).length < 2 ^ (prefixWord ++ tailWord_540351).sum := by decide
  have hdescent : baseEnd_540351 < baseStart_540351 := by decide
  rcases family_descends (prefixWord ++ tailWord_540351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540378 : List Nat := [3, 1, 1, 2, 2, 4, 3, 1, 3]
def baseStart_540378 : Nat := 118140960795 + 540378 * 2 ^ 59
def prefixEnd_540378 : Nat := 4983230072969 + 3 ^ 40 * 540378 * 2
def baseEnd_540378 : Nat := 246643243658126224257647

theorem tailTrace_540378 : CollatzResearch.WordTrace tailWord_540378 prefixEnd_540378 246643243658126224257647 := by
  unfold tailWord_540378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4927301209077567514997447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13139469890873513373326525 4927301209077567514997447)
  ·
    refine ⟨7390951813616351272496171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4927301209077567514997447 7390951813616351272496171)
    ·
      refine ⟨11086427720424526908744257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7390951813616351272496171 11086427720424526908744257)
      ·
        refine ⟨8314820790318395181558193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11086427720424526908744257 8314820790318395181558193)
        ·
          refine ⟨6236115592738796386168645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8314820790318395181558193 6236115592738796386168645)
          ·
            refine ⟨1169271673638524322406621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6236115592738796386168645 1169271673638524322406621)
            ·
              refine ⟨438476877614446620902483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1169271673638524322406621 438476877614446620902483)
              ·
                refine ⟨657715316421669931353725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438476877614446620902483 657715316421669931353725)
                ·
                  refine ⟨246643243658126224257647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657715316421669931353725 246643243658126224257647)
                  ·
                    rfl

theorem cell20_540378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_540378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540378 prefixEnd_540378 := by exact prefixLift 540378
  have htrace : WordTrace (prefixWord ++ tailWord_540378) baseStart_540378 baseEnd_540378 := by
    simpa [prefixWord, tailWord_540378, baseEnd_540378] using wordTrace_append hprefix tailTrace_540378
  have hstable : (prefixWord ++ tailWord_540378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540378).length < 2 ^ (prefixWord ++ tailWord_540378).sum := by decide
  have hdescent : baseEnd_540378 < baseStart_540378 := by decide
  rcases family_descends (prefixWord ++ tailWord_540378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540392 : List Nat := [2, 1, 4, 1, 3, 1, 4, 4]
def baseStart_540392 : Nat := 118140960795 + 540392 * 2 ^ 59
def prefixEnd_540392 : Nat := 4983230072969 + 3 ^ 40 * 540392 * 2
def baseEnd_540392 : Nat := 82216544546534799263641

theorem tailTrace_540392 : CollatzResearch.WordTrace tailWord_540392 prefixEnd_540392 82216544546534799263641 := by
  unfold tailWord_540392
  simp only [CollatzResearch.WordTrace]
  refine ⟨9854857729129775225499715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13139810305506366967332953 9854857729129775225499715)
  ·
    refine ⟨14782286593694662838249573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9854857729129775225499715 14782286593694662838249573)
    ·
      refine ⟨2771678736317749282171795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14782286593694662838249573 2771678736317749282171795)
      ·
        refine ⟨4157518104476623923257693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2771678736317749282171795 4157518104476623923257693)
        ·
          refine ⟨1559069289178733971221635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4157518104476623923257693 1559069289178733971221635)
          ·
            refine ⟨2338603933768100956832453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1559069289178733971221635 2338603933768100956832453)
            ·
              refine ⟨438488237581518929406085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2338603933768100956832453 438488237581518929406085)
              ·
                refine ⟨82216544546534799263641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 438488237581518929406085 82216544546534799263641)
                ·
                  rfl

theorem cell20_540392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_540392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540392 prefixEnd_540392 := by exact prefixLift 540392
  have htrace : WordTrace (prefixWord ++ tailWord_540392) baseStart_540392 baseEnd_540392 := by
    simpa [prefixWord, tailWord_540392, baseEnd_540392] using wordTrace_append hprefix tailTrace_540392
  have hstable : (prefixWord ++ tailWord_540392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540392).length < 2 ^ (prefixWord ++ tailWord_540392).sum := by decide
  have hdescent : baseEnd_540392 < baseStart_540392 := by decide
  rcases family_descends (prefixWord ++ tailWord_540392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540422 : List Nat := [6, 2, 2, 1, 1, 1, 2, 5]
def baseStart_540422 : Nat := 118140960795 + 540422 * 2 ^ 59
def prefixEnd_540422 : Nat := 4983230072969 + 3 ^ 40 * 540422 * 2
def baseEnd_540422 : Nat := 82221108819019208930267

theorem tailTrace_540422 : CollatzResearch.WordTrace tailWord_540422 prefixEnd_540422 82221108819019208930267 := by
  unfold tailWord_540422
  simp only [CollatzResearch.WordTrace]
  refine ⟨615962801504714549205985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13140539765433910383061013 615962801504714549205985)
  ·
    refine ⟨461972101128535911904489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 615962801504714549205985 461972101128535911904489)
    ·
      refine ⟨346479075846401933928367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 461972101128535911904489 346479075846401933928367)
      ·
        refine ⟨519718613769602900892551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346479075846401933928367 519718613769602900892551)
        ·
          refine ⟨779577920654404351338827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519718613769602900892551 779577920654404351338827)
          ·
            refine ⟨1169366880981606527008241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779577920654404351338827 1169366880981606527008241)
            ·
              refine ⟨877025160736204895256181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169366880981606527008241 877025160736204895256181)
              ·
                refine ⟨82221108819019208930267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 877025160736204895256181 82221108819019208930267)
                ·
                  rfl

theorem cell20_540422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_540422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540422 prefixEnd_540422 := by exact prefixLift 540422
  have htrace : WordTrace (prefixWord ++ tailWord_540422) baseStart_540422 baseEnd_540422 := by
    simpa [prefixWord, tailWord_540422, baseEnd_540422] using wordTrace_append hprefix tailTrace_540422
  have hstable : (prefixWord ++ tailWord_540422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540422).length < 2 ^ (prefixWord ++ tailWord_540422).sum := by decide
  have hdescent : baseEnd_540422 < baseStart_540422 := by decide
  rcases family_descends (prefixWord ++ tailWord_540422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540429 : List Nat := [1, 7, 2, 1, 1, 1, 1, 3, 3]
def baseStart_540429 : Nat := 118140960795 + 540429 * 2 ^ 59
def prefixEnd_540429 : Nat := 4983230072969 + 3 ^ 40 * 540429 * 2
def baseEnd_540429 : Nat := 246666521447796713557439

theorem tailTrace_540429 : CollatzResearch.WordTrace tailWord_540429 prefixEnd_540429 246666521447796713557439 := by
  unfold tailWord_540429
  simp only [CollatzResearch.WordTrace]
  refine ⟨19711064959125505770096341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13140709972750337180064227 19711064959125505770096341)
  ·
    refine ⟨461978084979504041486633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 19711064959125505770096341 461978084979504041486633)
    ·
      refine ⟨346483563734628031114975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 461978084979504041486633 346483563734628031114975)
      ·
        refine ⟨519725345601942046672463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346483563734628031114975 519725345601942046672463)
        ·
          refine ⟨779588018402913070008695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519725345601942046672463 779588018402913070008695)
          ·
            refine ⟨1169382027604369605013043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779588018402913070008695 1169382027604369605013043)
            ·
              refine ⟨1754073041406554407519565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1169382027604369605013043 1754073041406554407519565)
              ·
                refine ⟨657777390527457902819837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1754073041406554407519565 657777390527457902819837)
                ·
                  refine ⟨246666521447796713557439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657777390527457902819837 246666521447796713557439)
                  ·
                    rfl

theorem cell20_540429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_540429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540429 prefixEnd_540429 := by exact prefixLift 540429
  have htrace : WordTrace (prefixWord ++ tailWord_540429) baseStart_540429 baseEnd_540429 := by
    simpa [prefixWord, tailWord_540429, baseEnd_540429] using wordTrace_append hprefix tailTrace_540429
  have hstable : (prefixWord ++ tailWord_540429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540429).length < 2 ^ (prefixWord ++ tailWord_540429).sum := by decide
  have hdescent : baseEnd_540429 < baseStart_540429 := by decide
  rcases family_descends (prefixWord ++ tailWord_540429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540437 : List Nat := [1, 3, 2, 1, 2, 4, 1, 3, 3]
def baseStart_540437 : Nat := 118140960795 + 540437 * 2 ^ 59
def prefixEnd_540437 : Nat := 4983230072969 + 3 ^ 40 * 540437 * 2
def baseEnd_540437 : Nat := 246670172865784241290739

theorem tailTrace_540437 : CollatzResearch.WordTrace tailWord_540437 prefixEnd_540437 246670172865784241290739 := by
  unfold tailWord_540437
  simp only [CollatzResearch.WordTrace]
  refine ⟨19711356743096523136387565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13140904495397682090925043 19711356743096523136387565)
  ·
    refine ⟨7391758778661196176145337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19711356743096523136387565 7391758778661196176145337)
    ·
      refine ⟨5543819083995897132109003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7391758778661196176145337 5543819083995897132109003)
      ·
        refine ⟨8315728625993845698163505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5543819083995897132109003 8315728625993845698163505)
        ·
          refine ⟨6236796469495384273622629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8315728625993845698163505 6236796469495384273622629)
          ·
            refine ⟨1169399338030384551304243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6236796469495384273622629 1169399338030384551304243)
            ·
              refine ⟨1754099007045576826956365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1169399338030384551304243 1754099007045576826956365)
              ·
                refine ⟨657787127642091310108637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1754099007045576826956365 657787127642091310108637)
                ·
                  refine ⟨246670172865784241290739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657787127642091310108637 246670172865784241290739)
                  ·
                    rfl

theorem cell20_540437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_540437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540437 prefixEnd_540437 := by exact prefixLift 540437
  have htrace : WordTrace (prefixWord ++ tailWord_540437) baseStart_540437 baseEnd_540437 := by
    simpa [prefixWord, tailWord_540437, baseEnd_540437] using wordTrace_append hprefix tailTrace_540437
  have hstable : (prefixWord ++ tailWord_540437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540437).length < 2 ^ (prefixWord ++ tailWord_540437).sum := by decide
  have hdescent : baseEnd_540437 < baseStart_540437 := by decide
  rcases family_descends (prefixWord ++ tailWord_540437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540472 : List Nat := [2, 1, 2, 1, 3, 11]
def baseStart_540472 : Nat := 118140960795 + 540472 * 2 ^ 59
def prefixEnd_540472 : Nat := 4983230072969 + 3 ^ 40 * 540472 * 2
def baseEnd_540472 : Nat := 9136523993314062041627

theorem tailTrace_540472 : CollatzResearch.WordTrace tailWord_540472 prefixEnd_540472 9136523993314062041627 := by
  unfold tailWord_540472
  simp only [CollatzResearch.WordTrace]
  refine ⟨9856316648984862056955835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13141755531979816075941113 9856316648984862056955835)
  ·
    refine ⟨14784474973477293085433753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9856316648984862056955835 14784474973477293085433753)
    ·
      refine ⟨11088356230107969814075315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14784474973477293085433753 11088356230107969814075315)
      ·
        refine ⟨16632534345161954721112973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11088356230107969814075315 16632534345161954721112973)
        ·
          refine ⟨6237200379435733020417365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16632534345161954721112973 6237200379435733020417365)
          ·
            refine ⟨9136523993314062041627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6237200379435733020417365 9136523993314062041627)
            ·
              rfl

theorem cell20_540472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 11].length) (baseStart_540472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540472 prefixEnd_540472 := by exact prefixLift 540472
  have htrace : WordTrace (prefixWord ++ tailWord_540472) baseStart_540472 baseEnd_540472 := by
    simpa [prefixWord, tailWord_540472, baseEnd_540472] using wordTrace_append hprefix tailTrace_540472
  have hstable : (prefixWord ++ tailWord_540472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540472).length < 2 ^ (prefixWord ++ tailWord_540472).sum := by decide
  have hdescent : baseEnd_540472 < baseStart_540472 := by decide
  rcases family_descends (prefixWord ++ tailWord_540472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540478 : List Nat := [4, 2, 1, 2, 2, 2, 1, 4, 2]
def baseStart_540478 : Nat := 118140960795 + 540478 * 2 ^ 59
def prefixEnd_540478 : Nat := 4983230072969 + 3 ^ 40 * 540478 * 2
def baseEnd_540478 : Nat := 246688886382970320923905

theorem tailTrace_540478 : CollatzResearch.WordTrace tailWord_540478 prefixEnd_540478 246688886382970320923905 := by
  unfold tailWord_540478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2464106516993498392328761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13141901423965324759086725 2464106516993498392328761)
  ·
    refine ⟨1848079887745123794246571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2464106516993498392328761 1848079887745123794246571)
    ·
      refine ⟨2772119831617685691369857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1848079887745123794246571 2772119831617685691369857)
      ·
        refine ⟨2079089873713264268527393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2772119831617685691369857 2079089873713264268527393)
        ·
          refine ⟨1559317405284948201395545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2079089873713264268527393 1559317405284948201395545)
          ·
            refine ⟨1169488053963711151046659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1559317405284948201395545 1169488053963711151046659)
            ·
              refine ⟨1754232080945566726569989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1169488053963711151046659 1754232080945566726569989)
              ·
                refine ⟨328918515177293761231873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1754232080945566726569989 328918515177293761231873)
                ·
                  refine ⟨246688886382970320923905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328918515177293761231873 246688886382970320923905)
                  ·
                    rfl

theorem cell20_540478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_540478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540478 prefixEnd_540478 := by exact prefixLift 540478
  have htrace : WordTrace (prefixWord ++ tailWord_540478) baseStart_540478 baseEnd_540478 := by
    simpa [prefixWord, tailWord_540478, baseEnd_540478] using wordTrace_append hprefix tailTrace_540478
  have hstable : (prefixWord ++ tailWord_540478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540478).length < 2 ^ (prefixWord ++ tailWord_540478).sum := by decide
  have hdescent : baseEnd_540478 < baseStart_540478 := by decide
  rcases family_descends (prefixWord ++ tailWord_540478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540516 : List Nat := [2, 3, 1, 1, 5, 1, 2, 3, 2]
def baseStart_540516 : Nat := 118140960795 + 540516 * 2 ^ 59
def prefixEnd_540516 : Nat := 4983230072969 + 3 ^ 40 * 540516 * 2
def baseEnd_540516 : Nat := 246706230618411077657083

theorem tailTrace_540516 : CollatzResearch.WordTrace tailWord_540516 prefixEnd_540516 246706230618411077657083 := by
  unfold tailWord_540516
  simp only [CollatzResearch.WordTrace]
  refine ⟨9857119054905159814256701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13142825406540213085675601 9857119054905159814256701)
  ·
    refine ⟨3696419645589434930346263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9857119054905159814256701 3696419645589434930346263)
    ·
      refine ⟨5544629468384152395519395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3696419645589434930346263 5544629468384152395519395)
      ·
        refine ⟨8316944202576228593279093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5544629468384152395519395 8316944202576228593279093)
        ·
          refine ⟨779713518991521430619915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8316944202576228593279093 779713518991521430619915)
          ·
            refine ⟨1169570278487282145929873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 779713518991521430619915 1169570278487282145929873)
            ·
              refine ⟨877177708865461609447405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1169570278487282145929873 877177708865461609447405)
              ·
                refine ⟨328941640824548103542777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 877177708865461609447405 328941640824548103542777)
                ·
                  refine ⟨246706230618411077657083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328941640824548103542777 246706230618411077657083)
                  ·
                    rfl

theorem cell20_540516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_540516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540516 prefixEnd_540516 := by exact prefixLift 540516
  have htrace : WordTrace (prefixWord ++ tailWord_540516) baseStart_540516 baseEnd_540516 := by
    simpa [prefixWord, tailWord_540516, baseEnd_540516] using wordTrace_append hprefix tailTrace_540516
  have hstable : (prefixWord ++ tailWord_540516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540516).length < 2 ^ (prefixWord ++ tailWord_540516).sum := by decide
  have hdescent : baseEnd_540516 < baseStart_540516 := by decide
  rcases family_descends (prefixWord ++ tailWord_540516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540606 : List Nat := [4, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_540606 : Nat := 118140960795 + 540606 * 2 ^ 59
def prefixEnd_540606 : Nat := 4983230072969 + 3 ^ 40 * 540606 * 2
def baseEnd_540606 : Nat := 246747309070770764656715

theorem tailTrace_540606 : CollatzResearch.WordTrace tailWord_540606 prefixEnd_540606 246747309070770764656715 := by
  unfold tailWord_540606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2464690084935533124911209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13145013786322843332859781 2464690084935533124911209)
  ·
    refine ⟨1848517563701649843683407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2464690084935533124911209 1848517563701649843683407)
    ·
      refine ⟨2772776345552474765525111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1848517563701649843683407 2772776345552474765525111)
      ·
        refine ⟨4159164518328712148287667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2772776345552474765525111 4159164518328712148287667)
        ·
          refine ⟨6238746777493068222431501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4159164518328712148287667 6238746777493068222431501)
          ·
            refine ⟨2339530041559900583411813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6238746777493068222431501 2339530041559900583411813)
            ·
              refine ⟨438661882792481359389715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2339530041559900583411813 438661882792481359389715)
              ·
                refine ⟨657992824188722039084573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 438661882792481359389715 657992824188722039084573)
                ·
                  refine ⟨246747309070770764656715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 657992824188722039084573 246747309070770764656715)
                  ·
                    rfl

theorem cell20_540606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_540606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540606 prefixEnd_540606 := by exact prefixLift 540606
  have htrace : WordTrace (prefixWord ++ tailWord_540606) baseStart_540606 baseEnd_540606 := by
    simpa [prefixWord, tailWord_540606, baseEnd_540606] using wordTrace_append hprefix tailTrace_540606
  have hstable : (prefixWord ++ tailWord_540606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540606).length < 2 ^ (prefixWord ++ tailWord_540606).sum := by decide
  have hdescent : baseEnd_540606 < baseStart_540606 := by decide
  rcases family_descends (prefixWord ++ tailWord_540606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540624 : List Nat := [2, 1, 1, 1, 1, 2, 6, 6]
def baseStart_540624 : Nat := 118140960795 + 540624 * 2 ^ 59
def prefixEnd_540624 : Nat := 4983230072969 + 3 ^ 40 * 540624 * 2
def baseEnd_540624 : Nat := 82251841587080900685547

theorem tailTrace_540624 : CollatzResearch.WordTrace tailWord_540624 prefixEnd_540624 82251841587080900685547 := by
  unfold tailWord_540624
  simp only [CollatzResearch.WordTrace]
  refine ⟨9859088596709527036722463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13145451462279369382296617 9859088596709527036722463)
  ·
    refine ⟨14788632895064290555083695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9859088596709527036722463 14788632895064290555083695)
    ·
      refine ⟨22182949342596435832625543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14788632895064290555083695 22182949342596435832625543)
      ·
        refine ⟨33274424013894653748938315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22182949342596435832625543 33274424013894653748938315)
        ·
          refine ⟨49911636020841980623407473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33274424013894653748938315 49911636020841980623407473)
          ·
            refine ⟨37433727015631485467555605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49911636020841980623407473 37433727015631485467555605)
            ·
              refine ⟨1754705953857725881291669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37433727015631485467555605 1754705953857725881291669)
              ·
                refine ⟨82251841587080900685547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1754705953857725881291669 82251841587080900685547)
                ·
                  rfl

theorem cell20_540624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_540624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540624 prefixEnd_540624 := by exact prefixLift 540624
  have htrace : WordTrace (prefixWord ++ tailWord_540624) baseStart_540624 baseEnd_540624 := by
    simpa [prefixWord, tailWord_540624, baseEnd_540624] using wordTrace_append hprefix tailTrace_540624
  have hstable : (prefixWord ++ tailWord_540624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540624).length < 2 ^ (prefixWord ++ tailWord_540624).sum := by decide
  have hdescent : baseEnd_540624 < baseStart_540624 := by decide
  rcases family_descends (prefixWord ++ tailWord_540624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540647 : List Nat := [1, 1, 5, 2, 3, 2, 2, 2, 2]
def baseStart_540647 : Nat := 118140960795 + 540647 * 2 ^ 59
def prefixEnd_540647 : Nat := 4983230072969 + 3 ^ 40 * 540647 * 2
def baseEnd_540647 : Nat := 246766022587956844289881

theorem tailTrace_540647 : CollatzResearch.WordTrace tailWord_540647 prefixEnd_540647 246766022587956844289881 := by
  unfold tailWord_540647
  simp only [CollatzResearch.WordTrace]
  refine ⟨19719016072335729001532195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13146010714890486001021463 19719016072335729001532195)
  ·
    refine ⟨29578524108503593502298293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19719016072335729001532195 29578524108503593502298293)
    ·
      refine ⟨2772986635172211890840465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29578524108503593502298293 2772986635172211890840465)
      ·
        refine ⟨2079739976379158918130349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2772986635172211890840465 2079739976379158918130349)
        ·
          refine ⟨779902491142184594298881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2079739976379158918130349 779902491142184594298881)
          ·
            refine ⟨584926868356638445724161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 779902491142184594298881 584926868356638445724161)
            ·
              refine ⟨438695151267478834293121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584926868356638445724161 438695151267478834293121)
              ·
                refine ⟨329021363450609125719841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438695151267478834293121 329021363450609125719841)
                ·
                  refine ⟨246766022587956844289881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329021363450609125719841 246766022587956844289881)
                  ·
                    rfl

theorem cell20_540647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 2].length) (baseStart_540647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540647 prefixEnd_540647 := by exact prefixLift 540647
  have htrace : WordTrace (prefixWord ++ tailWord_540647) baseStart_540647 baseEnd_540647 := by
    simpa [prefixWord, tailWord_540647, baseEnd_540647] using wordTrace_append hprefix tailTrace_540647
  have hstable : (prefixWord ++ tailWord_540647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540647).length < 2 ^ (prefixWord ++ tailWord_540647).sum := by decide
  have hdescent : baseEnd_540647 < baseStart_540647 := by decide
  rcases family_descends (prefixWord ++ tailWord_540647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540655 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 4]
def baseStart_540655 : Nat := 118140960795 + 540655 * 2 ^ 59
def prefixEnd_540655 : Nat := 4983230072969 + 3 ^ 40 * 540655 * 2
def baseEnd_540655 : Nat := 246769674005944372023181

theorem tailTrace_540655 : CollatzResearch.WordTrace tailWord_540655 prefixEnd_540655 246769674005944372023181 := by
  unfold tailWord_540655
  simp only [CollatzResearch.WordTrace]
  refine ⟨19719307856306746367823419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13146205237537830911882279 19719307856306746367823419)
  ·
    refine ⟨29578961784460119551735129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19719307856306746367823419 29578961784460119551735129)
    ·
      refine ⟨22184221338345089663801347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29578961784460119551735129 22184221338345089663801347)
      ·
        refine ⟨33276332007517634495702021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22184221338345089663801347 33276332007517634495702021)
        ·
          refine ⟨6239312251409556467944129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33276332007517634495702021 6239312251409556467944129)
          ·
            refine ⟨4679484188557167350958097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6239312251409556467944129 4679484188557167350958097)
            ·
              refine ⟨3509613141417875513218573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4679484188557167350958097 3509613141417875513218573)
              ·
                refine ⟨1316104928031703317456965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3509613141417875513218573 1316104928031703317456965)
                ·
                  refine ⟨246769674005944372023181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1316104928031703317456965 246769674005944372023181)
                  ·
                    rfl

theorem cell20_540655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_540655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540655 prefixEnd_540655 := by exact prefixLift 540655
  have htrace : WordTrace (prefixWord ++ tailWord_540655) baseStart_540655 baseEnd_540655 := by
    simpa [prefixWord, tailWord_540655, baseEnd_540655] using wordTrace_append hprefix tailTrace_540655
  have hstable : (prefixWord ++ tailWord_540655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540655).length < 2 ^ (prefixWord ++ tailWord_540655).sum := by decide
  have hdescent : baseEnd_540655 < baseStart_540655 := by decide
  rcases family_descends (prefixWord ++ tailWord_540655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540686 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_540686 : Nat := 118140960795 + 540686 * 2 ^ 59
def prefixEnd_540686 : Nat := 4983230072969 + 3 ^ 40 * 540686 * 2
def baseEnd_540686 : Nat := 246783823250646041989721

theorem tailTrace_540686 : CollatzResearch.WordTrace tailWord_540686 prefixEnd_540686 246783823250646041989721 := by
  unfold tailWord_540686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2465054814899304832775239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13146959012796292441467941 2465054814899304832775239)
  ·
    refine ⟨3697582222348957249162859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2465054814899304832775239 3697582222348957249162859)
    ·
      refine ⟨5546373333523435873744289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3697582222348957249162859 5546373333523435873744289)
      ·
        refine ⟨4159780000142576905308217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5546373333523435873744289 4159780000142576905308217)
        ·
          refine ⟨3119835000106932678981163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4159780000142576905308217 3119835000106932678981163)
          ·
            refine ⟨4679752500160399018471745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3119835000106932678981163 4679752500160399018471745)
            ·
              refine ⟨3509814375120299263853809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4679752500160399018471745 3509814375120299263853809)
              ·
                refine ⟨2632360781340224447890357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3509814375120299263853809 2632360781340224447890357)
                ·
                  refine ⟨246783823250646041989721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2632360781340224447890357 246783823250646041989721)
                  ·
                    rfl

theorem cell20_540686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_540686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540686 prefixEnd_540686 := by exact prefixLift 540686
  have htrace : WordTrace (prefixWord ++ tailWord_540686) baseStart_540686 baseEnd_540686 := by
    simpa [prefixWord, tailWord_540686, baseEnd_540686] using wordTrace_append hprefix tailTrace_540686
  have hstable : (prefixWord ++ tailWord_540686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540686).length < 2 ^ (prefixWord ++ tailWord_540686).sum := by decide
  have hdescent : baseEnd_540686 < baseStart_540686 := by decide
  rcases family_descends (prefixWord ++ tailWord_540686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540734 : List Nat := [4, 2, 1, 3, 2, 1, 1, 6]
def baseStart_540734 : Nat := 118140960795 + 540734 * 2 ^ 59
def prefixEnd_540734 : Nat := 4983230072969 + 3 ^ 40 * 540734 * 2
def baseEnd_540734 : Nat := 82268577252857069463175

theorem tailTrace_540734 : CollatzResearch.WordTrace tailWord_540734 prefixEnd_540734 82268577252857069463175 := by
  unfold tailWord_540734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2465273652877567857493657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13148126148680361906632837 2465273652877567857493657)
  ·
    refine ⟨1848955239658175893120243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2465273652877567857493657 1848955239658175893120243)
    ·
      refine ⟨2773432859487263839680365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1848955239658175893120243 2773432859487263839680365)
      ·
        refine ⟨1040037322307723939880137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2773432859487263839680365 1040037322307723939880137)
        ·
          refine ⟨780027991730792954910103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1040037322307723939880137 780027991730792954910103)
          ·
            refine ⟨1170041987596189432365155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780027991730792954910103 1170041987596189432365155)
            ·
              refine ⟨1755062981394284148547733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1170041987596189432365155 1755062981394284148547733)
              ·
                refine ⟨82268577252857069463175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1755062981394284148547733 82268577252857069463175)
                ·
                  rfl

theorem cell20_540734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_540734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540734 prefixEnd_540734 := by exact prefixLift 540734
  have htrace : WordTrace (prefixWord ++ tailWord_540734) baseStart_540734 baseEnd_540734 := by
    simpa [prefixWord, tailWord_540734, baseEnd_540734] using wordTrace_append hprefix tailTrace_540734
  have hstable : (prefixWord ++ tailWord_540734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540734).length < 2 ^ (prefixWord ++ tailWord_540734).sum := by decide
  have hdescent : baseEnd_540734 < baseStart_540734 := by decide
  rcases family_descends (prefixWord ++ tailWord_540734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540745 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 7]
def baseStart_540745 : Nat := 118140960795 + 540745 * 2 ^ 59
def prefixEnd_540745 : Nat := 4983230072969 + 3 ^ 40 * 540745 * 2
def baseEnd_540745 : Nat := 246810752458304059022813

theorem tailTrace_540745 : CollatzResearch.WordTrace tailWord_540745 prefixEnd_540745 246810752458304059022813 := by
  unfold tailWord_540745
  simp only [CollatzResearch.WordTrace]
  refine ⟨19722590425980691738599689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13148393617320461159066459 19722590425980691738599689)
  ·
    refine ⟨14791942819485518803949767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19722590425980691738599689 14791942819485518803949767)
    ·
      refine ⟨22187914229228278205924651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14791942819485518803949767 22187914229228278205924651)
      ·
        refine ⟨33281871343842417308886977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22187914229228278205924651 33281871343842417308886977)
        ·
          refine ⟨24961403507881812981665233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33281871343842417308886977 24961403507881812981665233)
          ·
            refine ⟨18721052630911359736248925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24961403507881812981665233 18721052630911359736248925)
            ·
              refine ⟨7020394736591759901093347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18721052630911359736248925 7020394736591759901093347)
              ·
                refine ⟨10530592104887639851640021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7020394736591759901093347 10530592104887639851640021)
                ·
                  refine ⟨246810752458304059022813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10530592104887639851640021 246810752458304059022813)
                  ·
                    rfl

theorem cell20_540745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_540745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540745 prefixEnd_540745 := by exact prefixLift 540745
  have htrace : WordTrace (prefixWord ++ tailWord_540745) baseStart_540745 baseEnd_540745 := by
    simpa [prefixWord, tailWord_540745, baseEnd_540745] using wordTrace_append hprefix tailTrace_540745
  have hstable : (prefixWord ++ tailWord_540745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540745).length < 2 ^ (prefixWord ++ tailWord_540745).sum := by decide
  have hdescent : baseEnd_540745 < baseStart_540745 := by decide
  rcases family_descends (prefixWord ++ tailWord_540745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540758 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_540758 : Nat := 118140960795 + 540758 * 2 ^ 59
def prefixEnd_540758 : Nat := 4983230072969 + 3 ^ 40 * 540758 * 2
def baseEnd_540758 : Nat := 246816686012533791589427

theorem tailTrace_540758 : CollatzResearch.WordTrace tailWord_540758 prefixEnd_540758 246816686012533791589427 := by
  unfold tailWord_540758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1232691535933349684926433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13148709716622396639215285 1232691535933349684926433)
  ·
    refine ⟨924518651950012263694825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1232691535933349684926433 924518651950012263694825)
    ·
      refine ⟨693388988962509197771119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 924518651950012263694825 693388988962509197771119)
      ·
        refine ⟨1040083483443763796656679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 693388988962509197771119 1040083483443763796656679)
        ·
          refine ⟨1560125225165645694985019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040083483443763796656679 1560125225165645694985019)
          ·
            refine ⟨2340187837748468542477529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1560125225165645694985019 2340187837748468542477529)
            ·
              refine ⟨1755140878311351406858147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2340187837748468542477529 1755140878311351406858147)
              ·
                refine ⟨2632711317467027110287221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1755140878311351406858147 2632711317467027110287221)
                ·
                  refine ⟨246816686012533791589427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2632711317467027110287221 246816686012533791589427)
                  ·
                    rfl

theorem cell20_540758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_540758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540758 prefixEnd_540758 := by exact prefixLift 540758
  have htrace : WordTrace (prefixWord ++ tailWord_540758) baseStart_540758 baseEnd_540758 := by
    simpa [prefixWord, tailWord_540758, baseEnd_540758] using wordTrace_append hprefix tailTrace_540758
  have hstable : (prefixWord ++ tailWord_540758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540758).length < 2 ^ (prefixWord ++ tailWord_540758).sum := by decide
  have hdescent : baseEnd_540758 < baseStart_540758 := by decide
  rcases family_descends (prefixWord ++ tailWord_540758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540762 : List Nat := [3, 1, 1, 2, 1, 1, 4, 4, 3]
def baseStart_540762 : Nat := 118140960795 + 540762 * 2 ^ 59
def prefixEnd_540762 : Nat := 4983230072969 + 3 ^ 40 * 540762 * 2
def baseEnd_540762 : Nat := 246818511721527555456077

theorem tailTrace_540762 : CollatzResearch.WordTrace tailWord_540762 prefixEnd_540762 246818511721527555456077 := by
  unfold tailWord_540762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4930802616729775910492135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13148806977946069094645693 4930802616729775910492135)
  ·
    refine ⟨7396203925094663865738203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4930802616729775910492135 7396203925094663865738203)
    ·
      refine ⟨11094305887641995798607305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7396203925094663865738203 11094305887641995798607305)
      ·
        refine ⟨8320729415731496848955479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11094305887641995798607305 8320729415731496848955479)
        ·
          refine ⟨12481094123597245273433219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8320729415731496848955479 12481094123597245273433219)
          ·
            refine ⟨18721641185395867910149829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12481094123597245273433219 18721641185395867910149829)
            ·
              refine ⟨3510307722261725233153093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18721641185395867910149829 3510307722261725233153093)
              ·
                refine ⟨658182697924073481216205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3510307722261725233153093 658182697924073481216205)
                ·
                  refine ⟨246818511721527555456077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658182697924073481216205 246818511721527555456077)
                  ·
                    rfl

theorem cell20_540762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_540762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540762 prefixEnd_540762 := by exact prefixLift 540762
  have htrace : WordTrace (prefixWord ++ tailWord_540762) baseStart_540762 baseEnd_540762 := by
    simpa [prefixWord, tailWord_540762, baseEnd_540762] using wordTrace_append hprefix tailTrace_540762
  have hstable : (prefixWord ++ tailWord_540762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540762).length < 2 ^ (prefixWord ++ tailWord_540762).sum := by decide
  have hdescent : baseEnd_540762 < baseStart_540762 := by decide
  rcases family_descends (prefixWord ++ tailWord_540762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540765 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 4]
def baseStart_540765 : Nat := 118140960795 + 540765 * 2 ^ 59
def prefixEnd_540765 : Nat := 4983230072969 + 3 ^ 40 * 540765 * 2
def baseEnd_540765 : Nat := 246819881003272878356065

theorem tailTrace_540765 : CollatzResearch.WordTrace tailWord_540765 prefixEnd_540765 246819881003272878356065 := by
  unfold tailWord_540765
  simp only [CollatzResearch.WordTrace]
  refine ⟨19723319885908235154327749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13148879923938823436218499 19723319885908235154327749)
  ·
    refine ⟨3698122478607794091436453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19723319885908235154327749 3698122478607794091436453)
    ·
      refine ⟨693397964738961392144335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3698122478607794091436453 693397964738961392144335)
      ·
        refine ⟨1040096947108442088216503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 693397964738961392144335 1040096947108442088216503)
        ·
          refine ⟨1560145420662663132324755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040096947108442088216503 1560145420662663132324755)
          ·
            refine ⟨2340218130993994698487133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1560145420662663132324755 2340218130993994698487133)
            ·
              refine ⟨877581799122748011932675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2340218130993994698487133 877581799122748011932675)
              ·
                refine ⟨1316372698684122017899013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 877581799122748011932675 1316372698684122017899013)
                ·
                  refine ⟨246819881003272878356065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1316372698684122017899013 246819881003272878356065)
                  ·
                    rfl

theorem cell20_540765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_540765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540765 prefixEnd_540765 := by exact prefixLift 540765
  have htrace : WordTrace (prefixWord ++ tailWord_540765) baseStart_540765 baseEnd_540765 := by
    simpa [prefixWord, tailWord_540765, baseEnd_540765] using wordTrace_append hprefix tailTrace_540765
  have hstable : (prefixWord ++ tailWord_540765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540765).length < 2 ^ (prefixWord ++ tailWord_540765).sum := by decide
  have hdescent : baseEnd_540765 < baseStart_540765 := by decide
  rcases family_descends (prefixWord ++ tailWord_540765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540814 : List Nat := [4, 1, 1, 3, 11]
def baseStart_540814 : Nat := 118140960795 + 540814 * 2 ^ 59
def prefixEnd_540814 : Nat := 4983230072969 + 3 ^ 40 * 540814 * 2
def baseEnd_540814 : Nat := 3047435135042549206451

theorem tailTrace_540814 : CollatzResearch.WordTrace tailWord_540814 prefixEnd_540814 3047435135042549206451 := by
  unfold tailWord_540814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2465638382841339565357687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13150071375153811015240997 2465638382841339565357687)
  ·
    refine ⟨3698457574262009348036531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2465638382841339565357687 3698457574262009348036531)
    ·
      refine ⟨5547686361393014022054797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3698457574262009348036531 5547686361393014022054797)
      ·
        refine ⟨2080382385522380258270549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5547686361393014022054797 2080382385522380258270549)
        ·
          refine ⟨3047435135042549206451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2080382385522380258270549 3047435135042549206451)
          ·
            rfl

theorem cell20_540814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 11].length) (baseStart_540814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540814 prefixEnd_540814 := by exact prefixLift 540814
  have htrace : WordTrace (prefixWord ++ tailWord_540814) baseStart_540814 baseEnd_540814 := by
    simpa [prefixWord, tailWord_540814, baseEnd_540814] using wordTrace_append hprefix tailTrace_540814
  have hstable : (prefixWord ++ tailWord_540814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540814).length < 2 ^ (prefixWord ++ tailWord_540814).sum := by decide
  have hdescent : baseEnd_540814 < baseStart_540814 := by decide
  rcases family_descends (prefixWord ++ tailWord_540814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540831 : List Nat := [1, 1, 2, 6, 1, 1, 3, 5]
def baseStart_540831 : Nat := 118140960795 + 540831 * 2 ^ 59
def prefixEnd_540831 : Nat := 4983230072969 + 3 ^ 40 * 540831 * 2
def baseEnd_540831 : Nat := 82283335067223327385265

theorem tailTrace_540831 : CollatzResearch.WordTrace tailWord_540831 prefixEnd_540831 82283335067223327385265 := by
  unfold tailWord_540831
  simp only [CollatzResearch.WordTrace]
  refine ⟨19725727103669128426230347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13150484735779418950820231 19725727103669128426230347)
  ·
    refine ⟨29588590655503692639345521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19725727103669128426230347 29588590655503692639345521)
    ·
      refine ⟨22191442991627769479509141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29588590655503692639345521 22191442991627769479509141)
      ·
        refine ⟨1040223890232551694351991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22191442991627769479509141 1040223890232551694351991)
        ·
          refine ⟨1560335835348827541527987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040223890232551694351991 1560335835348827541527987)
          ·
            refine ⟨2340503753023241312291981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1560335835348827541527987 2340503753023241312291981)
            ·
              refine ⟨877688907383715492109493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2340503753023241312291981 877688907383715492109493)
              ·
                refine ⟨82283335067223327385265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 877688907383715492109493 82283335067223327385265)
                ·
                  rfl

theorem cell20_540831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 5].length) (baseStart_540831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540831 prefixEnd_540831 := by exact prefixLift 540831
  have htrace : WordTrace (prefixWord ++ tailWord_540831) baseStart_540831 baseEnd_540831 := by
    simpa [prefixWord, tailWord_540831, baseEnd_540831] using wordTrace_append hprefix tailTrace_540831
  have hstable : (prefixWord ++ tailWord_540831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540831).length < 2 ^ (prefixWord ++ tailWord_540831).sum := by decide
  have hdescent : baseEnd_540831 < baseStart_540831 := by decide
  rcases family_descends (prefixWord ++ tailWord_540831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540859 : List Nat := [1, 1, 1, 1, 1, 2, 6, 2, 5]
def baseStart_540859 : Nat := 118140960795 + 540859 * 2 ^ 59
def prefixEnd_540859 : Nat := 4983230072969 + 3 ^ 40 * 540859 * 2
def baseEnd_540859 : Nat := 246862785164626329222347

theorem tailTrace_540859 : CollatzResearch.WordTrace tailWord_540859 prefixEnd_540859 246862785164626329222347 := by
  unfold tailWord_540859
  simp only [CollatzResearch.WordTrace]
  refine ⟨19726748347567689208249631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13151165565045126138833087 19726748347567689208249631)
  ·
    refine ⟨29590122521351533812374447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19726748347567689208249631 29590122521351533812374447)
    ·
      refine ⟨44385183782027300718561671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29590122521351533812374447 44385183782027300718561671)
      ·
        refine ⟨66577775673040951077842507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44385183782027300718561671 66577775673040951077842507)
        ·
          refine ⟨99866663509561426616763761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66577775673040951077842507 99866663509561426616763761)
          ·
            refine ⟨74899997632171069962572821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99866663509561426616763761 74899997632171069962572821)
            ·
              refine ⟨3510937389008018904495601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74899997632171069962572821 3510937389008018904495601)
              ·
                refine ⟨2633203041756014178371701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3510937389008018904495601 2633203041756014178371701)
                ·
                  refine ⟨246862785164626329222347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2633203041756014178371701 246862785164626329222347)
                  ·
                    rfl

theorem cell20_540859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_540859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540859 prefixEnd_540859 := by exact prefixLift 540859
  have htrace : WordTrace (prefixWord ++ tailWord_540859) baseStart_540859 baseEnd_540859 := by
    simpa [prefixWord, tailWord_540859, baseEnd_540859] using wordTrace_append hprefix tailTrace_540859
  have hstable : (prefixWord ++ tailWord_540859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540859).length < 2 ^ (prefixWord ++ tailWord_540859).sum := by decide
  have hdescent : baseEnd_540859 < baseStart_540859 := by decide
  rcases family_descends (prefixWord ++ tailWord_540859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540914 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_540914 : Nat := 118140960795 + 540914 * 2 ^ 59
def prefixEnd_540914 : Nat := 4983230072969 + 3 ^ 40 * 540914 * 2
def baseEnd_540914 : Nat := 246887888663290582388789

theorem tailTrace_540914 : CollatzResearch.WordTrace tailWord_540914 prefixEnd_540914 246887888663290582388789 := by
  unfold tailWord_540914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4932188590592108400375449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13152502908245622401001197 4932188590592108400375449)
  ·
    refine ⟨3699141442944081300281587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4932188590592108400375449 3699141442944081300281587)
    ·
      refine ⟨5548712164416121950422381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3699141442944081300281587 5548712164416121950422381)
      ·
        refine ⟨2080767061656045731408393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5548712164416121950422381 2080767061656045731408393)
        ·
          refine ⟨1560575296242034298556295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2080767061656045731408393 1560575296242034298556295)
          ·
            refine ⟨2340862944363051447834443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1560575296242034298556295 2340862944363051447834443)
            ·
              refine ⟨3511294416544577171751665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2340862944363051447834443 3511294416544577171751665)
              ·
                refine ⟨2633470812408432878813749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3511294416544577171751665 2633470812408432878813749)
                ·
                  refine ⟨246887888663290582388789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2633470812408432878813749 246887888663290582388789)
                  ·
                    rfl

theorem cell20_540914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_540914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540914 prefixEnd_540914 := by exact prefixLift 540914
  have htrace : WordTrace (prefixWord ++ tailWord_540914) baseStart_540914 baseEnd_540914 := by
    simpa [prefixWord, tailWord_540914, baseEnd_540914] using wordTrace_append hprefix tailTrace_540914
  have hstable : (prefixWord ++ tailWord_540914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540914).length < 2 ^ (prefixWord ++ tailWord_540914).sum := by decide
  have hdescent : baseEnd_540914 < baseStart_540914 := by decide
  rcases family_descends (prefixWord ++ tailWord_540914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540938 : List Nat := [3, 1, 2, 2, 1, 1, 2, 6, 2]
def baseStart_540938 : Nat := 118140960795 + 540938 * 2 ^ 59
def prefixEnd_540938 : Nat := 4983230072969 + 3 ^ 40 * 540938 * 2
def baseEnd_540938 : Nat := 246898842917253165588691

theorem tailTrace_540938 : CollatzResearch.WordTrace tailWord_540938 prefixEnd_540938 246898842917253165588691 := by
  unfold tailWord_540938
  simp only [CollatzResearch.WordTrace]
  refine ⟨4932407428570371425093867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13153086476187657133583645 4932407428570371425093867)
  ·
    refine ⟨7398611142855557137640801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4932407428570371425093867 7398611142855557137640801)
    ·
      refine ⟨5548958357141667853230601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7398611142855557137640801 5548958357141667853230601)
      ·
        refine ⟨4161718767856250889922951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5548958357141667853230601 4161718767856250889922951)
        ·
          refine ⟨6242578151784376334884427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4161718767856250889922951 6242578151784376334884427)
          ·
            refine ⟨9363867227676564502326641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6242578151784376334884427 9363867227676564502326641)
            ·
              refine ⟨7022900420757423376744981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9363867227676564502326641 7022900420757423376744981)
              ·
                refine ⟨329198457223004220784921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7022900420757423376744981 329198457223004220784921)
                ·
                  refine ⟨246898842917253165588691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329198457223004220784921 246898842917253165588691)
                  ·
                    rfl

theorem cell20_540938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_540938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540938 prefixEnd_540938 := by exact prefixLift 540938
  have htrace : WordTrace (prefixWord ++ tailWord_540938) baseStart_540938 baseEnd_540938 := by
    simpa [prefixWord, tailWord_540938, baseEnd_540938] using wordTrace_append hprefix tailTrace_540938
  have hstable : (prefixWord ++ tailWord_540938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540938).length < 2 ^ (prefixWord ++ tailWord_540938).sum := by decide
  have hdescent : baseEnd_540938 < baseStart_540938 := by decide
  rcases family_descends (prefixWord ++ tailWord_540938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_540952 : List Nat := [2, 1, 2, 3, 1, 2, 3, 3, 3]
def baseStart_540952 : Nat := 118140960795 + 540952 * 2 ^ 59
def prefixEnd_540952 : Nat := 4983230072969 + 3 ^ 40 * 540952 * 2
def baseEnd_540952 : Nat := 246905232898731339121967

theorem tailTrace_540952 : CollatzResearch.WordTrace tailWord_540952 prefixEnd_540952 246905232898731339121967 := by
  unfold tailWord_540952
  simp only [CollatzResearch.WordTrace]
  refine ⟨9865070168115383045692555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13153426890820510727590073 9865070168115383045692555)
  ·
    refine ⟨14797605252173074568538833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9865070168115383045692555 14797605252173074568538833)
    ·
      refine ⟨11098203939129805926404125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14797605252173074568538833 11098203939129805926404125)
      ·
        refine ⟨4161826477173677222401547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11098203939129805926404125 4161826477173677222401547)
        ·
          refine ⟨6242739715760515833602321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4161826477173677222401547 6242739715760515833602321)
          ·
            refine ⟨4682054786820386875201741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6242739715760515833602321 4682054786820386875201741)
            ·
              refine ⟨1755770545057645078200653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4682054786820386875201741 1755770545057645078200653)
              ·
                refine ⟨658413954396616904325245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1755770545057645078200653 658413954396616904325245)
                ·
                  refine ⟨246905232898731339121967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658413954396616904325245 246905232898731339121967)
                  ·
                    rfl

theorem cell20_540952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_540952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_540952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_540952 prefixEnd_540952 := by exact prefixLift 540952
  have htrace : WordTrace (prefixWord ++ tailWord_540952) baseStart_540952 baseEnd_540952 := by
    simpa [prefixWord, tailWord_540952, baseEnd_540952] using wordTrace_append hprefix tailTrace_540952
  have hstable : (prefixWord ++ tailWord_540952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_540952).length < 2 ^ (prefixWord ++ tailWord_540952).sum := by decide
  have hdescent : baseEnd_540952 < baseStart_540952 := by decide
  rcases family_descends (prefixWord ++ tailWord_540952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541031 : List Nat := [1, 1, 5, 1, 3, 2, 2, 3, 2]
def baseStart_541031 : Nat := 118140960795 + 541031 * 2 ^ 59
def prefixEnd_541031 : Nat := 4983230072969 + 3 ^ 40 * 541031 * 2
def baseEnd_541031 : Nat := 246941290651358175488311

theorem tailTrace_541031 : CollatzResearch.WordTrace tailWord_541031 prefixEnd_541031 246941290651358175488311 := by
  unfold tailWord_541031
  simp only [CollatzResearch.WordTrace]
  refine ⟨19733021702944562583510947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13155347801963041722340631 19733021702944562583510947)
  ·
    refine ⟨29599532554416843875266421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19733021702944562583510947 29599532554416843875266421)
    ·
      refine ⟨2774956176976579113306227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29599532554416843875266421 2774956176976579113306227)
      ·
        refine ⟨4162434265464868669959341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2774956176976579113306227 4162434265464868669959341)
        ·
          refine ⟨1560912849549325751234753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4162434265464868669959341 1560912849549325751234753)
          ·
            refine ⟨1170684637161994313426065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1560912849549325751234753 1170684637161994313426065)
            ·
              refine ⟨878013477871495735069549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1170684637161994313426065 878013477871495735069549)
              ·
                refine ⟨329255054201810900651081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 878013477871495735069549 329255054201810900651081)
                ·
                  refine ⟨246941290651358175488311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329255054201810900651081 246941290651358175488311)
                  ·
                    rfl

theorem cell20_541031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 3, 2].length) (baseStart_541031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541031 prefixEnd_541031 := by exact prefixLift 541031
  have htrace : WordTrace (prefixWord ++ tailWord_541031) baseStart_541031 baseEnd_541031 := by
    simpa [prefixWord, tailWord_541031, baseEnd_541031] using wordTrace_append hprefix tailTrace_541031
  have hstable : (prefixWord ++ tailWord_541031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541031).length < 2 ^ (prefixWord ++ tailWord_541031).sum := by decide
  have hdescent : baseEnd_541031 < baseStart_541031 := by decide
  rcases family_descends (prefixWord ++ tailWord_541031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541042 : List Nat := [3, 2, 1, 2, 1, 4, 7]
def baseStart_541042 : Nat := 118140960795 + 541042 * 2 ^ 59
def prefixEnd_541042 : Nat := 4983230072969 + 3 ^ 40 * 541042 * 2
def baseEnd_541042 : Nat := 27438479039010114013511

theorem tailTrace_541042 : CollatzResearch.WordTrace tailWord_541042 prefixEnd_541042 27438479039010114013511 := by
  unfold tailWord_541042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4933355726476177865540345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13155615270603140974774253 4933355726476177865540345)
  ·
    refine ⟨3700016794857133399155259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4933355726476177865540345 3700016794857133399155259)
    ·
      refine ⟨5550025192285700098732889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3700016794857133399155259 5550025192285700098732889)
      ·
        refine ⟨4162518894214275074049667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5550025192285700098732889 4162518894214275074049667)
        ·
          refine ⟨6243778341321412611074501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4162518894214275074049667 6243778341321412611074501)
          ·
            refine ⟨1170708438997764864576469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6243778341321412611074501 1170708438997764864576469)
            ·
              refine ⟨27438479039010114013511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1170708438997764864576469 27438479039010114013511)
              ·
                rfl

theorem cell20_541042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 7].length) (baseStart_541042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541042 prefixEnd_541042 := by exact prefixLift 541042
  have htrace : WordTrace (prefixWord ++ tailWord_541042) baseStart_541042 baseEnd_541042 := by
    simpa [prefixWord, tailWord_541042, baseEnd_541042] using wordTrace_append hprefix tailTrace_541042
  have hstable : (prefixWord ++ tailWord_541042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541042).length < 2 ^ (prefixWord ++ tailWord_541042).sum := by decide
  have hdescent : baseEnd_541042 < baseStart_541042 := by decide
  rcases family_descends (prefixWord ++ tailWord_541042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541045 : List Nat := [1, 3, 4, 1, 2, 1, 3, 2, 3]
def baseStart_541045 : Nat := 118140960795 + 541045 * 2 ^ 59
def prefixEnd_541045 : Nat := 4983230072969 + 3 ^ 40 * 541045 * 2
def baseEnd_541045 : Nat := 246947680632836349021587

theorem tailTrace_541045 : CollatzResearch.WordTrace tailWord_541045 prefixEnd_541045 246947680632836349021587 := by
  unfold tailWord_541045
  simp only [CollatzResearch.WordTrace]
  refine ⟨19733532324893842974520589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13155688216595895316347059 19733532324893842974520589)
  ·
    refine ⟨7400074621835191115445221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19733532324893842974520589 7400074621835191115445221)
    ·
      refine ⟨1387513991594098334145979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7400074621835191115445221 1387513991594098334145979)
      ·
        refine ⟨2081270987391147501218969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1387513991594098334145979 2081270987391147501218969)
        ·
          refine ⟨1560953240543360625914227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2081270987391147501218969 1560953240543360625914227)
          ·
            refine ⟨2341429860815040938871341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1560953240543360625914227 2341429860815040938871341)
            ·
              refine ⟨878036197805640352076753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2341429860815040938871341 878036197805640352076753)
              ·
                refine ⟨658527148354230264057565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878036197805640352076753 658527148354230264057565)
                ·
                  refine ⟨246947680632836349021587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658527148354230264057565 246947680632836349021587)
                  ·
                    rfl

theorem cell20_541045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_541045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541045 prefixEnd_541045 := by exact prefixLift 541045
  have htrace : WordTrace (prefixWord ++ tailWord_541045) baseStart_541045 baseEnd_541045 := by
    simpa [prefixWord, tailWord_541045, baseEnd_541045] using wordTrace_append hprefix tailTrace_541045
  have hstable : (prefixWord ++ tailWord_541045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541045).length < 2 ^ (prefixWord ++ tailWord_541045).sum := by decide
  have hdescent : baseEnd_541045 < baseStart_541045 := by decide
  rcases family_descends (prefixWord ++ tailWord_541045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541086 : List Nat := [4, 3, 1, 2, 1, 1, 3, 3, 2]
def baseStart_541086 : Nat := 118140960795 + 541086 * 2 ^ 59
def prefixEnd_541086 : Nat := 4983230072969 + 3 ^ 40 * 541086 * 2
def baseEnd_541086 : Nat := 246966394150022428654753

theorem tailTrace_541086 : CollatzResearch.WordTrace tailWord_541086 prefixEnd_541086 246966394150022428654753 := by
  unfold tailWord_541086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2466878464718163372095389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13156685145163537984508741 2466878464718163372095389)
  ·
    refine ⟨925079424269311264535771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2466878464718163372095389 925079424269311264535771)
    ·
      refine ⟨1387619136403966896803657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 925079424269311264535771 1387619136403966896803657)
      ·
        refine ⟨1040714352302975172602743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1387619136403966896803657 1040714352302975172602743)
        ·
          refine ⟨1561071528454462758904115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040714352302975172602743 1561071528454462758904115)
          ·
            refine ⟨2341607292681694138356173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561071528454462758904115 2341607292681694138356173)
            ·
              refine ⟨878102734755635301883565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2341607292681694138356173 878102734755635301883565)
              ·
                refine ⟨329288525533363238206337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 878102734755635301883565 329288525533363238206337)
                ·
                  refine ⟨246966394150022428654753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329288525533363238206337 246966394150022428654753)
                  ·
                    rfl

theorem cell20_541086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_541086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541086 prefixEnd_541086 := by exact prefixLift 541086
  have htrace : WordTrace (prefixWord ++ tailWord_541086) baseStart_541086 baseEnd_541086 := by
    simpa [prefixWord, tailWord_541086, baseEnd_541086] using wordTrace_append hprefix tailTrace_541086
  have hstable : (prefixWord ++ tailWord_541086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541086).length < 2 ^ (prefixWord ++ tailWord_541086).sum := by decide
  have hdescent : baseEnd_541086 < baseStart_541086 := by decide
  rcases family_descends (prefixWord ++ tailWord_541086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541087 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 7]
def baseStart_541087 : Nat := 118140960795 + 541087 * 2 ^ 59
def prefixEnd_541087 : Nat := 4983230072969 + 3 ^ 40 * 541087 * 2
def baseEnd_541087 : Nat := 246966850577270869621415

theorem tailTrace_541087 : CollatzResearch.WordTrace tailWord_541087 prefixEnd_541087 246966850577270869621415 := by
  unfold tailWord_541087
  simp only [CollatzResearch.WordTrace]
  refine ⟨19735064190741684147549515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13156709460494456098366343 19735064190741684147549515)
  ·
    refine ⟨29602596286112526221324273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19735064190741684147549515 29602596286112526221324273)
    ·
      refine ⟨22201947214584394665993205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29602596286112526221324273 22201947214584394665993205)
      ·
        refine ⟨2081432551367286999936863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22201947214584394665993205 2081432551367286999936863)
        ·
          refine ⟨3122148827050930499905295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2081432551367286999936863 3122148827050930499905295)
          ·
            refine ⟨4683223240576395749857943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3122148827050930499905295 4683223240576395749857943)
            ·
              refine ⟨7024834860864593624786915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4683223240576395749857943 7024834860864593624786915)
              ·
                refine ⟨10537252291296890437180373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7024834860864593624786915 10537252291296890437180373)
                ·
                  refine ⟨246966850577270869621415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10537252291296890437180373 246966850577270869621415)
                  ·
                    rfl

theorem cell20_541087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_541087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541087 prefixEnd_541087 := by exact prefixLift 541087
  have htrace : WordTrace (prefixWord ++ tailWord_541087) baseStart_541087 baseEnd_541087 := by
    simpa [prefixWord, tailWord_541087, baseEnd_541087] using wordTrace_append hprefix tailTrace_541087
  have hstable : (prefixWord ++ tailWord_541087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541087).length < 2 ^ (prefixWord ++ tailWord_541087).sum := by decide
  have hdescent : baseEnd_541087 < baseStart_541087 := by decide
  rcases family_descends (prefixWord ++ tailWord_541087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541111 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 4]
def baseStart_541111 : Nat := 118140960795 + 541111 * 2 ^ 59
def prefixEnd_541111 : Nat := 4983230072969 + 3 ^ 40 * 541111 * 2
def baseEnd_541111 : Nat := 246977804831233452821317

theorem tailTrace_541111 : CollatzResearch.WordTrace tailWord_541111 prefixEnd_541111 246977804831233452821317 := by
  unfold tailWord_541111
  simp only [CollatzResearch.WordTrace]
  refine ⟨19735939542654736246423187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13157293028436490830948791 19735939542654736246423187)
  ·
    refine ⟨29603909313982104369634781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19735939542654736246423187 29603909313982104369634781)
    ·
      refine ⟨11101465992743289138613043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29603909313982104369634781 11101465992743289138613043)
      ·
        refine ⟨16652198989114933707919565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11101465992743289138613043 16652198989114933707919565)
        ·
          refine ⟨6244574620918100140469837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16652198989114933707919565 6244574620918100140469837)
          ·
            refine ⟨2341715482844287552676189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6244574620918100140469837 2341715482844287552676189)
            ·
              refine ⟨878143306066607832253571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2341715482844287552676189 878143306066607832253571)
              ·
                refine ⟨1317214959099911748380357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 878143306066607832253571 1317214959099911748380357)
                ·
                  refine ⟨246977804831233452821317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1317214959099911748380357 246977804831233452821317)
                  ·
                    rfl

theorem cell20_541111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_541111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541111 prefixEnd_541111 := by exact prefixLift 541111
  have htrace : WordTrace (prefixWord ++ tailWord_541111) baseStart_541111 baseEnd_541111 := by
    simpa [prefixWord, tailWord_541111, baseEnd_541111] using wordTrace_append hprefix tailTrace_541111
  have hstable : (prefixWord ++ tailWord_541111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541111).length < 2 ^ (prefixWord ++ tailWord_541111).sum := by decide
  have hdescent : baseEnd_541111 < baseStart_541111 := by decide
  rcases family_descends (prefixWord ++ tailWord_541111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541118 : List Nat := [4, 2, 1, 1, 1, 1, 3, 7]
def baseStart_541118 : Nat := 118140960795 + 541118 * 2 ^ 59
def prefixEnd_541118 : Nat := 4983230072969 + 3 ^ 40 * 541118 * 2
def baseEnd_541118 : Nat := 82326999940657513195985

theorem tailTrace_541118 : CollatzResearch.WordTrace tailWord_541118 prefixEnd_541118 82326999940657513195985 := by
  unfold tailWord_541118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2467024356703672055241001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13157463235752917627952005 2467024356703672055241001)
  ·
    refine ⟨1850268267527754041430751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2467024356703672055241001 1850268267527754041430751)
    ·
      refine ⟨2775402401291631062146127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1850268267527754041430751 2775402401291631062146127)
      ·
        refine ⟨4163103601937446593219191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2775402401291631062146127 4163103601937446593219191)
        ·
          refine ⟨6244655402906169889828787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4163103601937446593219191 6244655402906169889828787)
          ·
            refine ⟨9366983104359254834743181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6244655402906169889828787 9366983104359254834743181)
            ·
              refine ⟨3512618664134720563028693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9366983104359254834743181 3512618664134720563028693)
              ·
                refine ⟨82326999940657513195985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3512618664134720563028693 82326999940657513195985)
                ·
                  rfl

theorem cell20_541118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_541118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541118 prefixEnd_541118 := by exact prefixLift 541118
  have htrace : WordTrace (prefixWord ++ tailWord_541118) baseStart_541118 baseEnd_541118 := by
    simpa [prefixWord, tailWord_541118, baseEnd_541118] using wordTrace_append hprefix tailTrace_541118
  have hstable : (prefixWord ++ tailWord_541118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541118).length < 2 ^ (prefixWord ++ tailWord_541118).sum := by decide
  have hdescent : baseEnd_541118 < baseStart_541118 := by decide
  rcases family_descends (prefixWord ++ tailWord_541118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541162 : List Nat := [3, 1, 3, 1, 3, 3, 2, 2, 2]
def baseStart_541162 : Nat := 118140960795 + 541162 * 2 ^ 59
def prefixEnd_541162 : Nat := 4983230072969 + 3 ^ 40 * 541162 * 2
def baseEnd_541162 : Nat := 247001082620903942121109

theorem tailTrace_541162 : CollatzResearch.WordTrace tailWord_541162 prefixEnd_541162 247001082620903942121109 := by
  unfold tailWord_541162
  simp only [CollatzResearch.WordTrace]
  refine ⟨4934449916367492989132435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13158533110313314637686493 4934449916367492989132435)
  ·
    refine ⟨7401674874551239483698653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4934449916367492989132435 7401674874551239483698653)
    ·
      refine ⟨2775628077956714806386995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7401674874551239483698653 2775628077956714806386995)
      ·
        refine ⟨4163442116935072209580493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2775628077956714806386995 4163442116935072209580493)
        ·
          refine ⟨1561290793850652078592685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4163442116935072209580493 1561290793850652078592685)
          ·
            refine ⟨585484047693994529472257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1561290793850652078592685 585484047693994529472257)
            ·
              refine ⟨439113035770495897104193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 585484047693994529472257 439113035770495897104193)
              ·
                refine ⟨329334776827871922828145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439113035770495897104193 329334776827871922828145)
                ·
                  refine ⟨247001082620903942121109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329334776827871922828145 247001082620903942121109)
                  ·
                    rfl

theorem cell20_541162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_541162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541162 prefixEnd_541162 := by exact prefixLift 541162
  have htrace : WordTrace (prefixWord ++ tailWord_541162) baseStart_541162 baseEnd_541162 := by
    simpa [prefixWord, tailWord_541162, baseEnd_541162] using wordTrace_append hprefix tailTrace_541162
  have hstable : (prefixWord ++ tailWord_541162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541162).length < 2 ^ (prefixWord ++ tailWord_541162).sum := by decide
  have hdescent : baseEnd_541162 < baseStart_541162 := by decide
  rcases family_descends (prefixWord ++ tailWord_541162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541249 : List Nat := [1, 2, 5, 1, 1, 2, 4, 4]
def baseStart_541249 : Nat := 118140960795 + 541249 * 2 ^ 59
def prefixEnd_541249 : Nat := 4983230072969 + 3 ^ 40 * 541249 * 2
def baseEnd_541249 : Nat := 82346930597172768740251

theorem tailTrace_541249 : CollatzResearch.WordTrace tailWord_541249 prefixEnd_541249 82346930597172768740251 := by
  unfold tailWord_541249
  simp only [CollatzResearch.WordTrace]
  refine ⟨19740972816154785814946801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13160648544103190543297867 19740972816154785814946801)
  ·
    refine ⟨14805729612116089361210101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19740972816154785814946801 14805729612116089361210101)
    ·
      refine ⟨1388037151135883377613447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14805729612116089361210101 1388037151135883377613447)
      ·
        refine ⟨2082055726703825066420171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1388037151135883377613447 2082055726703825066420171)
        ·
          refine ⟨3123083590055737599630257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2082055726703825066420171 3123083590055737599630257)
          ·
            refine ⟨2342312692541803199722693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3123083590055737599630257 2342312692541803199722693)
            ·
              refine ⟨439183629851588099948005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2342312692541803199722693 439183629851588099948005)
              ·
                refine ⟨82346930597172768740251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 439183629851588099948005 82346930597172768740251)
                ·
                  rfl

theorem cell20_541249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 4].length) (baseStart_541249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541249 prefixEnd_541249 := by exact prefixLift 541249
  have htrace : WordTrace (prefixWord ++ tailWord_541249) baseStart_541249 baseEnd_541249 := by
    simpa [prefixWord, tailWord_541249, baseEnd_541249] using wordTrace_append hprefix tailTrace_541249
  have hstable : (prefixWord ++ tailWord_541249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541249).length < 2 ^ (prefixWord ++ tailWord_541249).sum := by decide
  have hdescent : baseEnd_541249 < baseStart_541249 := by decide
  rcases family_descends (prefixWord ++ tailWord_541249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541276 : List Nat := [2, 2, 4, 1, 3, 1, 3, 2, 2]
def baseStart_541276 : Nat := 118140960795 + 541276 * 2 ^ 59
def prefixEnd_541276 : Nat := 4983230072969 + 3 ^ 40 * 541276 * 2
def baseEnd_541276 : Nat := 247053115327226212320643

theorem tailTrace_541276 : CollatzResearch.WordTrace tailWord_541276 prefixEnd_541276 247053115327226212320643 := by
  unfold tailWord_541276
  simp only [CollatzResearch.WordTrace]
  refine ⟨9870978793528484713089841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13161305058037979617453121 9870978793528484713089841)
  ·
    refine ⟨7403234095146363534817381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9870978793528484713089841 7403234095146363534817381)
    ·
      refine ⟨1388106392839943162778259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7403234095146363534817381 1388106392839943162778259)
      ·
        refine ⟨2082159589259914744167389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1388106392839943162778259 2082159589259914744167389)
        ·
          refine ⟨780809845972468029062771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2082159589259914744167389 780809845972468029062771)
          ·
            refine ⟨1171214768958702043594157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780809845972468029062771 1171214768958702043594157)
            ·
              refine ⟨439205538359513266347809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1171214768958702043594157 439205538359513266347809)
              ·
                refine ⟨329404153769634949760857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439205538359513266347809 329404153769634949760857)
                ·
                  refine ⟨247053115327226212320643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329404153769634949760857 247053115327226212320643)
                  ·
                    rfl

theorem cell20_541276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_541276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541276 prefixEnd_541276 := by exact prefixLift 541276
  have htrace : WordTrace (prefixWord ++ tailWord_541276) baseStart_541276 baseEnd_541276 := by
    simpa [prefixWord, tailWord_541276, baseEnd_541276] using wordTrace_append hprefix tailTrace_541276
  have hstable : (prefixWord ++ tailWord_541276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541276).length < 2 ^ (prefixWord ++ tailWord_541276).sum := by decide
  have hdescent : baseEnd_541276 < baseStart_541276 := by decide
  rcases family_descends (prefixWord ++ tailWord_541276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541394 : List Nat := [3, 2, 2, 2, 3, 1, 2, 1, 4]
def baseStart_541394 : Nat := 118140960795 + 541394 * 2 ^ 59
def prefixEnd_541394 : Nat := 4983230072969 + 3 ^ 40 * 541394 * 2
def baseEnd_541394 : Nat := 247106973742542246386827

theorem tailTrace_541394 : CollatzResearch.WordTrace tailWord_541394 prefixEnd_541394 247106973742542246386827 := by
  unfold tailWord_541394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4936565350157368894743809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13164174267086317052650157 4936565350157368894743809)
  ·
    refine ⟨3702424012618026671057857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4936565350157368894743809 3702424012618026671057857)
    ·
      refine ⟨2776818009463520003293393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3702424012618026671057857 2776818009463520003293393)
      ·
        refine ⟨2082613507097640002470045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2776818009463520003293393 2082613507097640002470045)
        ·
          refine ⟨780980065161615000926267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2082613507097640002470045 780980065161615000926267)
          ·
            refine ⟨1171470097742422501389401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780980065161615000926267 1171470097742422501389401)
            ·
              refine ⟨878602573306816876042051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1171470097742422501389401 878602573306816876042051)
              ·
                refine ⟨1317903859960225314063077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 878602573306816876042051 1317903859960225314063077)
                ·
                  refine ⟨247106973742542246386827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1317903859960225314063077 247106973742542246386827)
                  ·
                    rfl

theorem cell20_541394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_541394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541394 prefixEnd_541394 := by exact prefixLift 541394
  have htrace : WordTrace (prefixWord ++ tailWord_541394) baseStart_541394 baseEnd_541394 := by
    simpa [prefixWord, tailWord_541394, baseEnd_541394] using wordTrace_append hprefix tailTrace_541394
  have hstable : (prefixWord ++ tailWord_541394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541394).length < 2 ^ (prefixWord ++ tailWord_541394).sum := by decide
  have hdescent : baseEnd_541394 < baseStart_541394 := by decide
  rcases family_descends (prefixWord ++ tailWord_541394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541404 : List Nat := [2, 2, 5, 1, 1, 2, 3, 1, 3]
def baseStart_541404 : Nat := 118140960795 + 541404 * 2 ^ 59
def prefixEnd_541404 : Nat := 4983230072969 + 3 ^ 40 * 541404 * 2
def baseEnd_541404 : Nat := 247111538015026656053453

theorem tailTrace_541404 : CollatzResearch.WordTrace tailWord_541404 prefixEnd_541404 247111538015026656053453 := by
  unfold tailWord_541404
  simp only [CollatzResearch.WordTrace]
  refine ⟨9873313065296623643419633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13164417420395498191226177 9873313065296623643419633)
  ·
    refine ⟨7404984798972467732564725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9873313065296623643419633 7404984798972467732564725)
    ·
      refine ⟨694217324903668849927943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7404984798972467732564725 694217324903668849927943)
      ·
        refine ⟨1041325987355503274891915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 694217324903668849927943 1041325987355503274891915)
        ·
          refine ⟨1561988981033254912337873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041325987355503274891915 1561988981033254912337873)
          ·
            refine ⟨1171491735774941184253405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1561988981033254912337873 1171491735774941184253405)
            ·
              refine ⟨439309400915602944095027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1171491735774941184253405 439309400915602944095027)
              ·
                refine ⟨658964101373404416142541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439309400915602944095027 658964101373404416142541)
                ·
                  refine ⟨247111538015026656053453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 658964101373404416142541 247111538015026656053453)
                  ·
                    rfl

theorem cell20_541404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_541404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541404 prefixEnd_541404 := by exact prefixLift 541404
  have htrace : WordTrace (prefixWord ++ tailWord_541404) baseStart_541404 baseEnd_541404 := by
    simpa [prefixWord, tailWord_541404, baseEnd_541404] using wordTrace_append hprefix tailTrace_541404
  have hstable : (prefixWord ++ tailWord_541404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541404).length < 2 ^ (prefixWord ++ tailWord_541404).sum := by decide
  have hdescent : baseEnd_541404 < baseStart_541404 := by decide
  rcases family_descends (prefixWord ++ tailWord_541404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541422 : List Nat := [4, 1, 2, 1, 1, 4, 1, 6]
def baseStart_541422 : Nat := 118140960795 + 541422 * 2 ^ 59
def prefixEnd_541422 : Nat := 4983230072969 + 3 ^ 40 * 541422 * 2
def baseEnd_541422 : Nat := 82373251235166197817793

theorem tailTrace_541422 : CollatzResearch.WordTrace tailWord_541422 prefixEnd_541422 82373251235166197817793 := by
  unfold tailWord_541422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2468410330566004545124315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13164855096352024240663013 2468410330566004545124315)
  ·
    refine ⟨3702615495849006817686473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2468410330566004545124315 3702615495849006817686473)
    ·
      refine ⟨2776961621886755113264855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3702615495849006817686473 2776961621886755113264855)
      ·
        refine ⟨4165442432830132669897283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2776961621886755113264855 4165442432830132669897283)
        ·
          refine ⟨6248163649245199004845925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4165442432830132669897283 6248163649245199004845925)
          ·
            refine ⟨1171530684233474813408611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6248163649245199004845925 1171530684233474813408611)
            ·
              refine ⟨1757296026350212220112917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1171530684233474813408611 1757296026350212220112917)
              ·
                refine ⟨82373251235166197817793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1757296026350212220112917 82373251235166197817793)
                ·
                  rfl

theorem cell20_541422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_541422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541422 prefixEnd_541422 := by exact prefixLift 541422
  have htrace : WordTrace (prefixWord ++ tailWord_541422) baseStart_541422 baseEnd_541422 := by
    simpa [prefixWord, tailWord_541422, baseEnd_541422] using wordTrace_append hprefix tailTrace_541422
  have hstable : (prefixWord ++ tailWord_541422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541422).length < 2 ^ (prefixWord ++ tailWord_541422).sum := by decide
  have hdescent : baseEnd_541422 < baseStart_541422 := by decide
  rcases family_descends (prefixWord ++ tailWord_541422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541488 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_541488 : Nat := 118140960795 + 541488 * 2 ^ 59
def prefixEnd_541488 : Nat := 4983230072969 + 3 ^ 40 * 541488 * 2
def baseEnd_541488 : Nat := 247149877903895697253109

theorem tailTrace_541488 : CollatzResearch.WordTrace tailWord_541488 prefixEnd_541488 247149877903895697253109 := by
  unfold tailWord_541488
  simp only [CollatzResearch.WordTrace]
  refine ⟨9874844931144464816448559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13166459908192619755264745 9874844931144464816448559)
  ·
    refine ⟨14812267396716697224672839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9874844931144464816448559 14812267396716697224672839)
    ·
      refine ⟨22218401095075045837009259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14812267396716697224672839 22218401095075045837009259)
      ·
        refine ⟨33327601642612568755513889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22218401095075045837009259 33327601642612568755513889)
        ·
          refine ⟨24995701231959426566635417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33327601642612568755513889 24995701231959426566635417)
          ·
            refine ⟨18746775923969569924976563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24995701231959426566635417 18746775923969569924976563)
            ·
              refine ⟨28120163885954354887464845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18746775923969569924976563 28120163885954354887464845)
              ·
                refine ⟨10545061457232883082799317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28120163885954354887464845 10545061457232883082799317)
                ·
                  refine ⟨247149877903895697253109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10545061457232883082799317 247149877903895697253109)
                  ·
                    rfl

theorem cell20_541488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_541488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541488 prefixEnd_541488 := by exact prefixLift 541488
  have htrace : WordTrace (prefixWord ++ tailWord_541488) baseStart_541488 baseEnd_541488 := by
    simpa [prefixWord, tailWord_541488, baseEnd_541488] using wordTrace_append hprefix tailTrace_541488
  have hstable : (prefixWord ++ tailWord_541488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541488).length < 2 ^ (prefixWord ++ tailWord_541488).sum := by decide
  have hdescent : baseEnd_541488 < baseStart_541488 := by decide
  rcases family_descends (prefixWord ++ tailWord_541488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541498 : List Nat := [3, 1, 1, 1, 7, 7]
def baseStart_541498 : Nat := 118140960795 + 541498 * 2 ^ 59
def prefixEnd_541498 : Nat := 4983230072969 + 3 ^ 40 * 541498 * 2
def baseEnd_541498 : Nat := 9153868228754818774805

theorem tailTrace_541498 : CollatzResearch.WordTrace tailWord_541498 prefixEnd_541498 9153868228754818774805 := by
  unfold tailWord_541498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4937513648063175335190287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13166703061501800893840765 4937513648063175335190287)
  ·
    refine ⟨7406270472094763002785431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4937513648063175335190287 7406270472094763002785431)
    ·
      refine ⟨11109405708142144504178147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7406270472094763002785431 11109405708142144504178147)
      ·
        refine ⟨16664108562213216756267221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11109405708142144504178147 16664108562213216756267221)
        ·
          refine ⟨390565044426872267725013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16664108562213216756267221 390565044426872267725013)
          ·
            refine ⟨9153868228754818774805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 390565044426872267725013 9153868228754818774805)
            ·
              rfl

theorem cell20_541498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 7].length) (baseStart_541498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541498 prefixEnd_541498 := by exact prefixLift 541498
  have htrace : WordTrace (prefixWord ++ tailWord_541498) baseStart_541498 baseEnd_541498 := by
    simpa [prefixWord, tailWord_541498, baseEnd_541498] using wordTrace_append hprefix tailTrace_541498
  have hstable : (prefixWord ++ tailWord_541498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541498).length < 2 ^ (prefixWord ++ tailWord_541498).sum := by decide
  have hdescent : baseEnd_541498 < baseStart_541498 := by decide
  rcases family_descends (prefixWord ++ tailWord_541498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541501 : List Nat := [1, 4, 1, 4, 2, 1, 2, 2, 3]
def baseStart_541501 : Nat := 118140960795 + 541501 * 2 ^ 59
def prefixEnd_541501 : Nat := 4983230072969 + 3 ^ 40 * 541501 * 2
def baseEnd_541501 : Nat := 247155811458125429819723

theorem tailTrace_541501 : CollatzResearch.WordTrace tailWord_541501 prefixEnd_541501 247155811458125429819723 := by
  unfold tailWord_541501
  simp only [CollatzResearch.WordTrace]
  refine ⟨19750164011241832853120357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13166776007494555235413571 19750164011241832853120357)
  ·
    refine ⟨3703155752107843659960067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19750164011241832853120357 3703155752107843659960067)
    ·
      refine ⟨5554733628161765489940101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3703155752107843659960067 5554733628161765489940101)
      ·
        refine ⟨1041512555280331029363769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5554733628161765489940101 1041512555280331029363769)
        ·
          refine ⟨781134416460248272022827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1041512555280331029363769 781134416460248272022827)
          ·
            refine ⟨1171701624690372408034241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781134416460248272022827 1171701624690372408034241)
            ·
              refine ⟨878776218517779306025681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1171701624690372408034241 878776218517779306025681)
              ·
                refine ⟨659082163888334479519261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878776218517779306025681 659082163888334479519261)
                ·
                  refine ⟨247155811458125429819723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659082163888334479519261 247155811458125429819723)
                  ·
                    rfl

theorem cell20_541501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_541501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541501 prefixEnd_541501 := by exact prefixLift 541501
  have htrace : WordTrace (prefixWord ++ tailWord_541501) baseStart_541501 baseEnd_541501 := by
    simpa [prefixWord, tailWord_541501, baseEnd_541501] using wordTrace_append hprefix tailTrace_541501
  have hstable : (prefixWord ++ tailWord_541501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541501).length < 2 ^ (prefixWord ++ tailWord_541501).sum := by decide
  have hdescent : baseEnd_541501 < baseStart_541501 := by decide
  rcases family_descends (prefixWord ++ tailWord_541501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541512 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 4]
def baseStart_541512 : Nat := 118140960795 + 541512 * 2 ^ 59
def prefixEnd_541512 : Nat := 4983230072969 + 3 ^ 40 * 541512 * 2
def baseEnd_541512 : Nat := 247160832157858280453011

theorem tailTrace_541512 : CollatzResearch.WordTrace tailWord_541512 prefixEnd_541512 247160832157858280453011 := by
  unfold tailWord_541512
  simp only [CollatzResearch.WordTrace]
  refine ⟨9875282607100990865885395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13167043476134654487847193 9875282607100990865885395)
  ·
    refine ⟨14812923910651486298828093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9875282607100990865885395 14812923910651486298828093)
    ·
      refine ⟨5554846466494307362060535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14812923910651486298828093 5554846466494307362060535)
      ·
        refine ⟨8332269699741461043090803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5554846466494307362060535 8332269699741461043090803)
        ·
          refine ⟨12498404549612191564636205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8332269699741461043090803 12498404549612191564636205)
          ·
            refine ⟨4686901706104571836738577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12498404549612191564636205 4686901706104571836738577)
            ·
              refine ⟨3515176279578428877553933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4686901706104571836738577 3515176279578428877553933)
              ·
                refine ⟨1318191104841910829082725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3515176279578428877553933 1318191104841910829082725)
                ·
                  refine ⟨247160832157858280453011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1318191104841910829082725 247160832157858280453011)
                  ·
                    rfl

theorem cell20_541512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_541512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541512 prefixEnd_541512 := by exact prefixLift 541512
  have htrace : WordTrace (prefixWord ++ tailWord_541512) baseStart_541512 baseEnd_541512 := by
    simpa [prefixWord, tailWord_541512, baseEnd_541512] using wordTrace_append hprefix tailTrace_541512
  have hstable : (prefixWord ++ tailWord_541512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541512).length < 2 ^ (prefixWord ++ tailWord_541512).sum := by decide
  have hdescent : baseEnd_541512 < baseStart_541512 := by decide
  rcases family_descends (prefixWord ++ tailWord_541512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541536 : List Nat := [2, 1, 1, 3, 3, 1, 5, 4]
def baseStart_541536 : Nat := 118140960795 + 541536 * 2 ^ 59
def prefixEnd_541536 : Nat := 4983230072969 + 3 ^ 40 * 541536 * 2
def baseEnd_541536 : Nat := 82390595470606954550971

theorem tailTrace_541536 : CollatzResearch.WordTrace tailWord_541536 prefixEnd_541536 82390595470606954550971 := by
  unfold tailWord_541536
  simp only [CollatzResearch.WordTrace]
  refine ⟨9875720283057516915322231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13167627044076689220429641 9875720283057516915322231)
  ·
    refine ⟨14813580424586275372983347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9875720283057516915322231 14813580424586275372983347)
    ·
      refine ⟨22220370636879413059475021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14813580424586275372983347 22220370636879413059475021)
      ·
        refine ⟨8332638988829779897303133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22220370636879413059475021 8332638988829779897303133)
        ·
          refine ⟨3124739620811167461488675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8332638988829779897303133 3124739620811167461488675)
          ·
            refine ⟨4687109431216751192233013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3124739620811167461488675 4687109431216751192233013)
            ·
              refine ⟨439416509176570424271845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4687109431216751192233013 439416509176570424271845)
              ·
                refine ⟨82390595470606954550971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 439416509176570424271845 82390595470606954550971)
                ·
                  rfl

theorem cell20_541536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_541536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541536 prefixEnd_541536 := by exact prefixLift 541536
  have htrace : WordTrace (prefixWord ++ tailWord_541536) baseStart_541536 baseEnd_541536 := by
    simpa [prefixWord, tailWord_541536, baseEnd_541536] using wordTrace_append hprefix tailTrace_541536
  have hstable : (prefixWord ++ tailWord_541536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541536).length < 2 ^ (prefixWord ++ tailWord_541536).sum := by decide
  have hdescent : baseEnd_541536 < baseStart_541536 := by decide
  rcases family_descends (prefixWord ++ tailWord_541536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541567 : List Nat := [1, 1, 2, 2, 1, 1, 6, 4, 2]
def baseStart_541567 : Nat := 118140960795 + 541567 * 2 ^ 59
def prefixEnd_541567 : Nat := 4983230072969 + 3 ^ 40 * 541567 * 2
def baseEnd_541567 : Nat := 247185935656522533619453

theorem tailTrace_541567 : CollatzResearch.WordTrace tailWord_541567 prefixEnd_541567 247185935656522533619453 := by
  unfold tailWord_541567
  simp only [CollatzResearch.WordTrace]
  refine ⟨19752571229002726125022955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13168380819335150750015303 19752571229002726125022955)
  ·
    refine ⟨29628856843504089187534433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19752571229002726125022955 29628856843504089187534433)
    ·
      refine ⟨22221642632628066890650825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29628856843504089187534433 22221642632628066890650825)
      ·
        refine ⟨16666231974471050167988119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22221642632628066890650825 16666231974471050167988119)
        ·
          refine ⟨24999347961706575251982179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16666231974471050167988119 24999347961706575251982179)
          ·
            refine ⟨37499021942559862877973269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24999347961706575251982179 37499021942559862877973269)
            ·
              refine ⟨1757766653557493572404997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37499021942559862877973269 1757766653557493572404997)
              ·
                refine ⟨329581247542030044825937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1757766653557493572404997 329581247542030044825937)
                ·
                  refine ⟨247185935656522533619453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329581247542030044825937 247185935656522533619453)
                  ·
                    rfl

theorem cell20_541567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 4, 2].length) (baseStart_541567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541567 prefixEnd_541567 := by exact prefixLift 541567
  have htrace : WordTrace (prefixWord ++ tailWord_541567) baseStart_541567 baseEnd_541567 := by
    simpa [prefixWord, tailWord_541567, baseEnd_541567] using wordTrace_append hprefix tailTrace_541567
  have hstable : (prefixWord ++ tailWord_541567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541567).length < 2 ^ (prefixWord ++ tailWord_541567).sum := by decide
  have hdescent : baseEnd_541567 < baseStart_541567 := by decide
  rcases family_descends (prefixWord ++ tailWord_541567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541601 : List Nat := [1, 2, 3, 4, 1, 3, 1, 3, 2]
def baseStart_541601 : Nat := 118140960795 + 541601 * 2 ^ 59
def prefixEnd_541601 : Nat := 4983230072969 + 3 ^ 40 * 541601 * 2
def baseEnd_541601 : Nat := 247201454182969526485981

theorem tailTrace_541601 : CollatzResearch.WordTrace tailWord_541601 prefixEnd_541601 247201454182969526485981 := by
  unfold tailWord_541601
  simp only [CollatzResearch.WordTrace]
  refine ⟨19753811310879549931760657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13169207540586366621173771 19753811310879549931760657)
  ·
    refine ⟨14815358483159662448820493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19753811310879549931760657 14815358483159662448820493)
    ·
      refine ⟨5555759431184873418307685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14815358483159662448820493 5555759431184873418307685)
      ·
        refine ⟨1041704893347163765932691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5555759431184873418307685 1041704893347163765932691)
        ·
          refine ⟨1562557340020745648899037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041704893347163765932691 1562557340020745648899037)
          ·
            refine ⟨585959002507779618337139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1562557340020745648899037 585959002507779618337139)
            ·
              refine ⟨878938503761669427505709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585959002507779618337139 878938503761669427505709)
              ·
                refine ⟨329601938910626035314641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 878938503761669427505709 329601938910626035314641)
                ·
                  refine ⟨247201454182969526485981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329601938910626035314641 247201454182969526485981)
                  ·
                    rfl

theorem cell20_541601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 2].length) (baseStart_541601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541601 prefixEnd_541601 := by exact prefixLift 541601
  have htrace : WordTrace (prefixWord ++ tailWord_541601) baseStart_541601 baseEnd_541601 := by
    simpa [prefixWord, tailWord_541601, baseEnd_541601] using wordTrace_append hprefix tailTrace_541601
  have hstable : (prefixWord ++ tailWord_541601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541601).length < 2 ^ (prefixWord ++ tailWord_541601).sum := by decide
  have hdescent : baseEnd_541601 < baseStart_541601 := by decide
  rcases family_descends (prefixWord ++ tailWord_541601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541650 : List Nat := [3, 2, 2, 3, 1, 1, 2, 6]
def baseStart_541650 : Nat := 118140960795 + 541650 * 2 ^ 59
def prefixEnd_541650 : Nat := 4983230072969 + 3 ^ 40 * 541650 * 2
def baseEnd_541650 : Nat := 82407939706047711284149

theorem tailTrace_541650 : CollatzResearch.WordTrace tailWord_541650 prefixEnd_541650 82407939706047711284149 := by
  unfold tailWord_541650
  simp only [CollatzResearch.WordTrace]
  refine ⟨4938899621925507825073601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13170398991801354200196269 4938899621925507825073601)
  ·
    refine ⟨3704174716444130868805201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4938899621925507825073601 3704174716444130868805201)
    ·
      refine ⟨2778131037333098151603901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3704174716444130868805201 2778131037333098151603901)
      ·
        refine ⟨1041799138999911806851463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2778131037333098151603901 1041799138999911806851463)
        ·
          refine ⟨1562698708499867710277195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1041799138999911806851463 1562698708499867710277195)
          ·
            refine ⟨2344048062749801565415793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562698708499867710277195 2344048062749801565415793)
            ·
              refine ⟨1758036047062351174061845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2344048062749801565415793 1758036047062351174061845)
              ·
                refine ⟨82407939706047711284149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1758036047062351174061845 82407939706047711284149)
                ·
                  rfl

theorem cell20_541650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_541650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541650 prefixEnd_541650 := by exact prefixLift 541650
  have htrace : WordTrace (prefixWord ++ tailWord_541650) baseStart_541650 baseEnd_541650 := by
    simpa [prefixWord, tailWord_541650, baseEnd_541650] using wordTrace_append hprefix tailTrace_541650
  have hstable : (prefixWord ++ tailWord_541650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541650).length < 2 ^ (prefixWord ++ tailWord_541650).sum := by decide
  have hdescent : baseEnd_541650 < baseStart_541650 := by decide
  rcases family_descends (prefixWord ++ tailWord_541650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541671 : List Nat := [1, 1, 5, 2, 2, 9]
def baseStart_541671 : Nat := 118140960795 + 541671 * 2 ^ 59
def prefixEnd_541671 : Nat := 4983230072969 + 3 ^ 40 * 541671 * 2
def baseEnd_541671 : Nat := 9156792744087422005643

theorem tailTrace_541671 : CollatzResearch.WordTrace tailWord_541671 prefixEnd_541671 9156792744087422005643 := by
  unfold tailWord_541671
  simp only [CollatzResearch.WordTrace]
  refine ⟨19756364420625951886808867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13170909613750634591205911 19756364420625951886808867)
  ·
    refine ⟨29634546630938927830213301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19756364420625951886808867 29634546630938927830213301)
    ·
      refine ⟨2778238746650524484082497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29634546630938927830213301 2778238746650524484082497)
      ·
        refine ⟨2083679059987893363061873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2778238746650524484082497 2083679059987893363061873)
        ·
          refine ⟨1562759294990920022296405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2083679059987893363061873 1562759294990920022296405)
          ·
            refine ⟨9156792744087422005643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1562759294990920022296405 9156792744087422005643)
            ·
              rfl

theorem cell20_541671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 9].length) (baseStart_541671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541671 prefixEnd_541671 := by exact prefixLift 541671
  have htrace : WordTrace (prefixWord ++ tailWord_541671) baseStart_541671 baseEnd_541671 := by
    simpa [prefixWord, tailWord_541671, baseEnd_541671] using wordTrace_append hprefix tailTrace_541671
  have hstable : (prefixWord ++ tailWord_541671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541671).length < 2 ^ (prefixWord ++ tailWord_541671).sum := by decide
  have hdescent : baseEnd_541671 < baseStart_541671 := by decide
  rcases family_descends (prefixWord ++ tailWord_541671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541674 : List Nat := [3, 1, 3, 1, 2, 3, 2, 2, 3]
def baseStart_541674 : Nat := 118140960795 + 541674 * 2 ^ 59
def prefixEnd_541674 : Nat := 4983230072969 + 3 ^ 40 * 541674 * 2
def baseEnd_541674 : Nat := 247234773372105717052349

theorem tailTrace_541674 : CollatzResearch.WordTrace tailWord_541674 prefixEnd_541674 247234773372105717052349 := by
  unfold tailWord_541674
  simp only [CollatzResearch.WordTrace]
  refine ⟨4939118459903770849792019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13170982559743388932778717 4939118459903770849792019)
  ·
    refine ⟨7408677689855656274688029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4939118459903770849792019 7408677689855656274688029)
    ·
      refine ⟨2778254133695871103008011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7408677689855656274688029 2778254133695871103008011)
      ·
        refine ⟨4167381200543806654512017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2778254133695871103008011 4167381200543806654512017)
        ·
          refine ⟨3125535900407854990884013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4167381200543806654512017 3125535900407854990884013)
          ·
            refine ⟨1172075962652945621581505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3125535900407854990884013 1172075962652945621581505)
            ·
              refine ⟨879056971989709216186129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1172075962652945621581505 879056971989709216186129)
              ·
                refine ⟨659292728992281912139597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 879056971989709216186129 659292728992281912139597)
                ·
                  refine ⟨247234773372105717052349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659292728992281912139597 247234773372105717052349)
                  ·
                    rfl

theorem cell20_541674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_541674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541674 prefixEnd_541674 := by exact prefixLift 541674
  have htrace : WordTrace (prefixWord ++ tailWord_541674) baseStart_541674 baseEnd_541674 := by
    simpa [prefixWord, tailWord_541674, baseEnd_541674] using wordTrace_append hprefix tailTrace_541674
  have hstable : (prefixWord ++ tailWord_541674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541674).length < 2 ^ (prefixWord ++ tailWord_541674).sum := by decide
  have hdescent : baseEnd_541674 < baseStart_541674 := by decide
  rcases family_descends (prefixWord ++ tailWord_541674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541740 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 4]
def baseStart_541740 : Nat := 118140960795 + 541740 * 2 ^ 59
def prefixEnd_541740 : Nat := 4983230072969 + 3 ^ 40 * 541740 * 2
def baseEnd_541740 : Nat := 247264897570502820852079

theorem tailTrace_541740 : CollatzResearch.WordTrace tailWord_541740 prefixEnd_541740 247264897570502820852079 := by
  unfold tailWord_541740
  simp only [CollatzResearch.WordTrace]
  refine ⟨9879440528687988335535337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13172587371583984447380449 9879440528687988335535337)
  ·
    refine ⟨7409580396515991251651503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9879440528687988335535337 7409580396515991251651503)
    ·
      refine ⟨11114370594773986877477255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7409580396515991251651503 11114370594773986877477255)
      ·
        refine ⟨16671555892160980316215883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11114370594773986877477255 16671555892160980316215883)
        ·
          refine ⟨25007333838241470474323825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16671555892160980316215883 25007333838241470474323825)
          ·
            refine ⟨18755500378681102855742869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25007333838241470474323825 18755500378681102855742869)
            ·
              refine ⟨879164080250676696362947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18755500378681102855742869 879164080250676696362947)
              ·
                refine ⟨1318746120376015044544421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879164080250676696362947 1318746120376015044544421)
                ·
                  refine ⟨247264897570502820852079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1318746120376015044544421 247264897570502820852079)
                  ·
                    rfl

theorem cell20_541740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_541740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541740 prefixEnd_541740 := by exact prefixLift 541740
  have htrace : WordTrace (prefixWord ++ tailWord_541740) baseStart_541740 baseEnd_541740 := by
    simpa [prefixWord, tailWord_541740, baseEnd_541740] using wordTrace_append hprefix tailTrace_541740
  have hstable : (prefixWord ++ tailWord_541740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541740).length < 2 ^ (prefixWord ++ tailWord_541740).sum := by decide
  have hdescent : baseEnd_541740 < baseStart_541740 := by decide
  rcases family_descends (prefixWord ++ tailWord_541740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541792 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_541792 : Nat := 118140960795 + 541792 * 2 ^ 59
def prefixEnd_541792 : Nat := 4983230072969 + 3 ^ 40 * 541792 * 2
def baseEnd_541792 : Nat := 247288631787421751118533

theorem tailTrace_541792 : CollatzResearch.WordTrace tailWord_541792 prefixEnd_541792 247288631787421751118533 := by
  unfold tailWord_541792
  simp only [CollatzResearch.WordTrace]
  refine ⟨9880388826593794775981815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13173851768791726367975753 9880388826593794775981815)
  ·
    refine ⟨14820583239890692163972723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9880388826593794775981815 14820583239890692163972723)
    ·
      refine ⟨22230874859836038245959085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14820583239890692163972723 22230874859836038245959085)
      ·
        refine ⟨8336578072438514342234657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22230874859836038245959085 8336578072438514342234657)
        ·
          refine ⟨6252433554328885756675993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8336578072438514342234657 6252433554328885756675993)
          ·
            refine ⟨4689325165746664317506995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6252433554328885756675993 4689325165746664317506995)
            ·
              refine ⟨7033987748619996476260493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4689325165746664317506995 7033987748619996476260493)
              ·
                refine ⟨2637745405732498678597685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7033987748619996476260493 2637745405732498678597685)
                ·
                  refine ⟨247288631787421751118533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2637745405732498678597685 247288631787421751118533)
                  ·
                    rfl

theorem cell20_541792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_541792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541792 prefixEnd_541792 := by exact prefixLift 541792
  have htrace : WordTrace (prefixWord ++ tailWord_541792) baseStart_541792 baseEnd_541792 := by
    simpa [prefixWord, tailWord_541792, baseEnd_541792] using wordTrace_append hprefix tailTrace_541792
  have hstable : (prefixWord ++ tailWord_541792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541792).length < 2 ^ (prefixWord ++ tailWord_541792).sum := by decide
  have hdescent : baseEnd_541792 < baseStart_541792 := by decide
  rcases family_descends (prefixWord ++ tailWord_541792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541802 : List Nat := [3, 1, 3, 2, 2, 2, 2, 5]
def baseStart_541802 : Nat := 118140960795 + 541802 * 2 ^ 59
def prefixEnd_541802 : Nat := 4983230072969 + 3 ^ 40 * 541802 * 2
def baseEnd_541802 : Nat := 82431065353302053595053

theorem tailTrace_541802 : CollatzResearch.WordTrace tailWord_541802 prefixEnd_541802 82431065353302053595053 := by
  unfold tailWord_541802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4940285595787840314956915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13174094922100907506551773 4940285595787840314956915)
  ·
    refine ⟨7410428393681760472435373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4940285595787840314956915 7410428393681760472435373)
    ·
      refine ⟨2778910647630660177163265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7410428393681760472435373 2778910647630660177163265)
      ·
        refine ⟨2084182985722995132872449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2778910647630660177163265 2084182985722995132872449)
        ·
          refine ⟨1563137239292246349654337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2084182985722995132872449 1563137239292246349654337)
          ·
            refine ⟨1172352929469184762240753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1563137239292246349654337 1172352929469184762240753)
            ·
              refine ⟨879264697101888571680565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1172352929469184762240753 879264697101888571680565)
              ·
                refine ⟨82431065353302053595053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 879264697101888571680565 82431065353302053595053)
                ·
                  rfl

theorem cell20_541802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_541802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541802 prefixEnd_541802 := by exact prefixLift 541802
  have htrace : WordTrace (prefixWord ++ tailWord_541802) baseStart_541802 baseEnd_541802 := by
    simpa [prefixWord, tailWord_541802, baseEnd_541802] using wordTrace_append hprefix tailTrace_541802
  have hstable : (prefixWord ++ tailWord_541802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541802).length < 2 ^ (prefixWord ++ tailWord_541802).sum := by decide
  have hdescent : baseEnd_541802 < baseStart_541802 := by decide
  rcases family_descends (prefixWord ++ tailWord_541802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541805 : List Nat := [1, 5, 1, 1, 2, 4, 2, 1, 3]
def baseStart_541805 : Nat := 118140960795 + 541805 * 2 ^ 59
def prefixEnd_541805 : Nat := 4983230072969 + 3 ^ 40 * 541805 * 2
def baseEnd_541805 : Nat := 247294565341651483685147

theorem tailTrace_541805 : CollatzResearch.WordTrace tailWord_541805 prefixEnd_541805 247294565341651483685147 := by
  unfold tailWord_541805
  simp only [CollatzResearch.WordTrace]
  refine ⟨19761251802140492772186869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13174167868093661848124579 19761251802140492772186869)
  ·
    refine ⟨1852617356450671197392519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19761251802140492772186869 1852617356450671197392519)
    ·
      refine ⟨2778926034676006796088779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1852617356450671197392519 2778926034676006796088779)
      ·
        refine ⟨4168389052014010194133169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2778926034676006796088779 4168389052014010194133169)
        ·
          refine ⟨3126291789010507645599877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4168389052014010194133169 3126291789010507645599877)
          ·
            refine ⟨586179710439470183549977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3126291789010507645599877 586179710439470183549977)
            ·
              refine ⟨439634782829602637662483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586179710439470183549977 439634782829602637662483)
              ·
                refine ⟨659452174244403956493725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439634782829602637662483 659452174244403956493725)
                ·
                  refine ⟨247294565341651483685147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659452174244403956493725 247294565341651483685147)
                  ·
                    rfl

theorem cell20_541805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_541805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541805 prefixEnd_541805 := by exact prefixLift 541805
  have htrace : WordTrace (prefixWord ++ tailWord_541805) baseStart_541805 baseEnd_541805 := by
    simpa [prefixWord, tailWord_541805, baseEnd_541805] using wordTrace_append hprefix tailTrace_541805
  have hstable : (prefixWord ++ tailWord_541805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541805).length < 2 ^ (prefixWord ++ tailWord_541805).sum := by decide
  have hdescent : baseEnd_541805 < baseStart_541805 := by decide
  rcases family_descends (prefixWord ++ tailWord_541805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541847 : List Nat := [1, 1, 3, 3, 3, 1, 1, 4, 3]
def baseStart_541847 : Nat := 118140960795 + 541847 * 2 ^ 59
def prefixEnd_541847 : Nat := 4983230072969 + 3 ^ 40 * 541847 * 2
def baseEnd_541847 : Nat := 247313735286086004284975

theorem tailTrace_541847 : CollatzResearch.WordTrace tailWord_541847 prefixEnd_541847 247313735286086004284975 := by
  unfold tailWord_541847
  simp only [CollatzResearch.WordTrace]
  refine ⟨19762783667988333945215795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13175189111992222630143863 19762783667988333945215795)
  ·
    refine ⟨29644175501982500917823693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19762783667988333945215795 29644175501982500917823693)
    ·
      refine ⟨11116565813243437844183885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29644175501982500917823693 11116565813243437844183885)
      ·
        refine ⟨4168712179966289191568957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11116565813243437844183885 4168712179966289191568957)
        ·
          refine ⟨1563267067487358446838359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4168712179966289191568957 1563267067487358446838359)
          ·
            refine ⟨2344900601231037670257539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563267067487358446838359 2344900601231037670257539)
            ·
              refine ⟨3517350901846556505386309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2344900601231037670257539 3517350901846556505386309)
              ·
                refine ⟨659503294096229344759933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3517350901846556505386309 659503294096229344759933)
                ·
                  refine ⟨247313735286086004284975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659503294096229344759933 247313735286086004284975)
                  ·
                    rfl

theorem cell20_541847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 3].length) (baseStart_541847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541847 prefixEnd_541847 := by exact prefixLift 541847
  have htrace : WordTrace (prefixWord ++ tailWord_541847) baseStart_541847 baseEnd_541847 := by
    simpa [prefixWord, tailWord_541847, baseEnd_541847] using wordTrace_append hprefix tailTrace_541847
  have hstable : (prefixWord ++ tailWord_541847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541847).length < 2 ^ (prefixWord ++ tailWord_541847).sum := by decide
  have hdescent : baseEnd_541847 < baseStart_541847 := by decide
  rcases family_descends (prefixWord ++ tailWord_541847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541850 : List Nat := [3, 1, 1, 5, 1, 2, 1, 4, 2]
def baseStart_541850 : Nat := 118140960795 + 541850 * 2 ^ 59
def prefixEnd_541850 : Nat := 4983230072969 + 3 ^ 40 * 541850 * 2
def baseEnd_541850 : Nat := 247315104567831327184963

theorem tailTrace_541850 : CollatzResearch.WordTrace tailWord_541850 prefixEnd_541850 247315104567831327184963 := by
  unfold tailWord_541850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4940723271744366364393751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13175262057984976971716669 4940723271744366364393751)
  ·
    refine ⟨7411084907616549546590627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4940723271744366364393751 7411084907616549546590627)
    ·
      refine ⟨11116627361424824319885941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7411084907616549546590627 11116627361424824319885941)
      ·
        refine ⟨1042183815133577279989307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11116627361424824319885941 1042183815133577279989307)
        ·
          refine ⟨1563275722700365919983961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042183815133577279989307 1563275722700365919983961)
          ·
            refine ⟨1172456792025274439987971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1563275722700365919983961 1172456792025274439987971)
            ·
              refine ⟨1758685188037911659981957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172456792025274439987971 1758685188037911659981957)
              ·
                refine ⟨329753472757108436246617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1758685188037911659981957 329753472757108436246617)
                ·
                  refine ⟨247315104567831327184963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329753472757108436246617 247315104567831327184963)
                  ·
                    rfl

theorem cell20_541850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_541850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541850 prefixEnd_541850 := by exact prefixLift 541850
  have htrace : WordTrace (prefixWord ++ tailWord_541850) baseStart_541850 baseEnd_541850 := by
    simpa [prefixWord, tailWord_541850, baseEnd_541850] using wordTrace_append hprefix tailTrace_541850
  have hstable : (prefixWord ++ tailWord_541850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541850).length < 2 ^ (prefixWord ++ tailWord_541850).sum := by decide
  have hdescent : baseEnd_541850 < baseStart_541850 := by decide
  rcases family_descends (prefixWord ++ tailWord_541850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541861 : List Nat := [1, 3, 1, 2, 1, 4, 3, 5]
def baseStart_541861 : Nat := 118140960795 + 541861 * 2 ^ 59
def prefixEnd_541861 : Nat := 4983230072969 + 3 ^ 40 * 541861 * 2
def baseEnd_541861 : Nat := 82440041755854725939417

theorem tailTrace_541861 : CollatzResearch.WordTrace tailWord_541861 prefixEnd_541861 82440041755854725939417 := by
  unfold tailWord_541861
  simp only [CollatzResearch.WordTrace]
  refine ⟨19763294289937614336225437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13175529526625076224150291 19763294289937614336225437)
  ·
    refine ⟨7411235358726605376084539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19763294289937614336225437 7411235358726605376084539)
    ·
      refine ⟨11116853038089908064126809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7411235358726605376084539 11116853038089908064126809)
      ·
        refine ⟨8337639778567431048095107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11116853038089908064126809 8337639778567431048095107)
        ·
          refine ⟨12506459667851146572142661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8337639778567431048095107 12506459667851146572142661)
          ·
            refine ⟨2344961187722089982276749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12506459667851146572142661 2344961187722089982276749)
            ·
              refine ⟨879360445395783743353781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2344961187722089982276749 879360445395783743353781)
              ·
                refine ⟨82440041755854725939417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 879360445395783743353781 82440041755854725939417)
                ·
                  rfl

theorem cell20_541861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 5].length) (baseStart_541861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541861 prefixEnd_541861 := by exact prefixLift 541861
  have htrace : WordTrace (prefixWord ++ tailWord_541861) baseStart_541861 baseEnd_541861 := by
    simpa [prefixWord, tailWord_541861, baseEnd_541861] using wordTrace_append hprefix tailTrace_541861
  have hstable : (prefixWord ++ tailWord_541861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541861).length < 2 ^ (prefixWord ++ tailWord_541861).sum := by decide
  have hdescent : baseEnd_541861 < baseStart_541861 := by decide
  rcases family_descends (prefixWord ++ tailWord_541861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541875 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 6]
def baseStart_541875 : Nat := 118140960795 + 541875 * 2 ^ 59
def prefixEnd_541875 : Nat := 4983230072969 + 3 ^ 40 * 541875 * 2
def baseEnd_541875 : Nat := 247326515249042351351527

theorem tailTrace_541875 : CollatzResearch.WordTrace tailWord_541875 prefixEnd_541875 247326515249042351351527 := by
  unfold tailWord_541875
  simp only [CollatzResearch.WordTrace]
  refine ⟨19763804911886894727235079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13175869941257929818156719 19763804911886894727235079)
  ·
    refine ⟨29645707367830342090852619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19763804911886894727235079 29645707367830342090852619)
    ·
      refine ⟨44468561051745513136278929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29645707367830342090852619 44468561051745513136278929)
      ·
        refine ⟨33351420788809134852209197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44468561051745513136278929 33351420788809134852209197)
        ·
          refine ⟨12506782795803425569578449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33351420788809134852209197 12506782795803425569578449)
          ·
            refine ⟨9380087096852569177183837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12506782795803425569578449 9380087096852569177183837)
            ·
              refine ⟨3517532661319713441443939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9380087096852569177183837 3517532661319713441443939)
              ·
                refine ⟨5276298991979570162165909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3517532661319713441443939 5276298991979570162165909)
                ·
                  refine ⟨247326515249042351351527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5276298991979570162165909 247326515249042351351527)
                  ·
                    rfl

theorem cell20_541875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_541875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541875 prefixEnd_541875 := by exact prefixLift 541875
  have htrace : WordTrace (prefixWord ++ tailWord_541875) baseStart_541875 baseEnd_541875 := by
    simpa [prefixWord, tailWord_541875, baseEnd_541875] using wordTrace_append hprefix tailTrace_541875
  have hstable : (prefixWord ++ tailWord_541875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541875).length < 2 ^ (prefixWord ++ tailWord_541875).sum := by decide
  have hdescent : baseEnd_541875 < baseStart_541875 := by decide
  rcases family_descends (prefixWord ++ tailWord_541875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541888 : List Nat := [2, 1, 1, 2, 6, 1, 2, 3, 2]
def baseStart_541888 : Nat := 118140960795 + 541888 * 2 ^ 59
def prefixEnd_541888 : Nat := 4983230072969 + 3 ^ 40 * 541888 * 2
def baseEnd_541888 : Nat := 247332448803272083918141

theorem tailTrace_541888 : CollatzResearch.WordTrace tailWord_541888 prefixEnd_541888 247332448803272083918141 := by
  unfold tailWord_541888
  simp only [CollatzResearch.WordTrace]
  refine ⟨9882139530419898973729159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13176186040559865298305545 9882139530419898973729159)
  ·
    refine ⟨14823209295629848460593739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9882139530419898973729159 14823209295629848460593739)
    ·
      refine ⟨22234813943444772690890609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14823209295629848460593739 22234813943444772690890609)
      ·
        refine ⟨16676110457583579518167957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22234813943444772690890609 16676110457583579518167957)
        ·
          refine ⟨781692677699230289914123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16676110457583579518167957 781692677699230289914123)
          ·
            refine ⟨1172539016548845434871185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781692677699230289914123 1172539016548845434871185)
            ·
              refine ⟨879404262411634076153389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1172539016548845434871185 879404262411634076153389)
              ·
                refine ⟨329776598404362778557521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 879404262411634076153389 329776598404362778557521)
                ·
                  refine ⟨247332448803272083918141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329776598404362778557521 247332448803272083918141)
                  ·
                    rfl

theorem cell20_541888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3, 2].length) (baseStart_541888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541888 prefixEnd_541888 := by exact prefixLift 541888
  have htrace : WordTrace (prefixWord ++ tailWord_541888) baseStart_541888 baseEnd_541888 := by
    simpa [prefixWord, tailWord_541888, baseEnd_541888] using wordTrace_append hprefix tailTrace_541888
  have hstable : (prefixWord ++ tailWord_541888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541888).length < 2 ^ (prefixWord ++ tailWord_541888).sum := by decide
  have hdescent : baseEnd_541888 < baseStart_541888 := by decide
  rcases family_descends (prefixWord ++ tailWord_541888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541894 : List Nat := [6, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_541894 : Nat := 118140960795 + 541894 * 2 ^ 59
def prefixEnd_541894 : Nat := 4983230072969 + 3 ^ 40 * 541894 * 2
def baseEnd_541894 : Nat := 247335187366762729718117

theorem tailTrace_541894 : CollatzResearch.WordTrace tailWord_541894 prefixEnd_541894 247335187366762729718117 := by
  unfold tailWord_541894
  simp only [CollatzResearch.WordTrace]
  refine ⟨617640559338064405380523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13176331932545373981451157 617640559338064405380523)
  ·
    refine ⟨926460839007096608070785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 617640559338064405380523 926460839007096608070785)
    ·
      refine ⟨694845629255322456053089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 926460839007096608070785 694845629255322456053089)
      ·
        refine ⟨521134221941491842039817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 694845629255322456053089 521134221941491842039817)
        ·
          refine ⟨390850666456118881529863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 521134221941491842039817 390850666456118881529863)
          ·
            refine ⟨586275999684178322294795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390850666456118881529863 586275999684178322294795)
            ·
              refine ⟨879413999526267483442193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586275999684178322294795 879413999526267483442193)
              ·
                refine ⟨659560499644700612581645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 879413999526267483442193 659560499644700612581645)
                ·
                  refine ⟨247335187366762729718117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659560499644700612581645 247335187366762729718117)
                  ·
                    rfl

theorem cell20_541894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_541894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541894 prefixEnd_541894 := by exact prefixLift 541894
  have htrace : WordTrace (prefixWord ++ tailWord_541894) baseStart_541894 baseEnd_541894 := by
    simpa [prefixWord, tailWord_541894, baseEnd_541894] using wordTrace_append hprefix tailTrace_541894
  have hstable : (prefixWord ++ tailWord_541894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541894).length < 2 ^ (prefixWord ++ tailWord_541894).sum := by decide
  have hdescent : baseEnd_541894 < baseStart_541894 := by decide
  rcases family_descends (prefixWord ++ tailWord_541894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541909 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 4]
def baseStart_541909 : Nat := 118140960795 + 541909 * 2 ^ 59
def prefixEnd_541909 : Nat := 4983230072969 + 3 ^ 40 * 541909 * 2
def baseEnd_541909 : Nat := 247342033775489344218055

theorem tailTrace_541909 : CollatzResearch.WordTrace tailWord_541909 prefixEnd_541909 247342033775489344218055 := by
  unfold tailWord_541909
  simp only [CollatzResearch.WordTrace]
  refine ⟨19765044993763718533972781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13176696662509145689315187 19765044993763718533972781)
  ·
    refine ⟨7411891872661394450239793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19765044993763718533972781 7411891872661394450239793)
    ·
      refine ⟨5558918904496045837679845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7411891872661394450239793 5558918904496045837679845)
      ·
        refine ⟨1042297294593008594564971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5558918904496045837679845 1042297294593008594564971)
        ·
          refine ⟨1563445941889512891847457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042297294593008594564971 1563445941889512891847457)
          ·
            refine ⟨1172584456417134668885593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1563445941889512891847457 1172584456417134668885593)
            ·
              refine ⟨879438342312851001664195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1172584456417134668885593 879438342312851001664195)
              ·
                refine ⟨1319157513469276502496293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879438342312851001664195 1319157513469276502496293)
                ·
                  refine ⟨247342033775489344218055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1319157513469276502496293 247342033775489344218055)
                  ·
                    rfl

theorem cell20_541909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_541909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541909 prefixEnd_541909 := by exact prefixLift 541909
  have htrace : WordTrace (prefixWord ++ tailWord_541909) baseStart_541909 baseEnd_541909 := by
    simpa [prefixWord, tailWord_541909, baseEnd_541909] using wordTrace_append hprefix tailTrace_541909
  have hstable : (prefixWord ++ tailWord_541909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541909).length < 2 ^ (prefixWord ++ tailWord_541909).sum := by decide
  have hdescent : baseEnd_541909 < baseStart_541909 := by decide
  rcases family_descends (prefixWord ++ tailWord_541909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541930 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_541930 : Nat := 118140960795 + 541930 * 2 ^ 59
def prefixEnd_541930 : Nat := 4983230072969 + 3 ^ 40 * 541930 * 2
def baseEnd_541930 : Nat := 247351618747706604517969

theorem tailTrace_541930 : CollatzResearch.WordTrace tailWord_541930 prefixEnd_541930 247351618747706604517969 := by
  unfold tailWord_541930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4941452731671909780121811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13177207284458426080324829 4941452731671909780121811)
  ·
    refine ⟨7412179097507864670182717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4941452731671909780121811 7412179097507864670182717)
    ·
      refine ⟨2779567161565449251318519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7412179097507864670182717 2779567161565449251318519)
      ·
        refine ⟨4169350742348173876977779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2779567161565449251318519 4169350742348173876977779)
        ·
          refine ⟨6254026113522260815466669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4169350742348173876977779 6254026113522260815466669)
          ·
            refine ⟨2345259792570847805800001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6254026113522260815466669 2345259792570847805800001)
            ·
              refine ⟨1758944844428135854350001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2345259792570847805800001 1758944844428135854350001)
              ·
                refine ⟨1319208633321101890762501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1758944844428135854350001 1319208633321101890762501)
                ·
                  refine ⟨247351618747706604517969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1319208633321101890762501 247351618747706604517969)
                  ·
                    rfl

theorem cell20_541930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_541930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541930 prefixEnd_541930 := by exact prefixLift 541930
  have htrace : WordTrace (prefixWord ++ tailWord_541930) baseStart_541930 baseEnd_541930 := by
    simpa [prefixWord, tailWord_541930, baseEnd_541930] using wordTrace_append hprefix tailTrace_541930
  have hstable : (prefixWord ++ tailWord_541930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541930).length < 2 ^ (prefixWord ++ tailWord_541930).sum := by decide
  have hdescent : baseEnd_541930 < baseStart_541930 := by decide
  rcases family_descends (prefixWord ++ tailWord_541930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541933 : List Nat := [1, 5, 1, 2, 2, 3, 2, 4]
def baseStart_541933 : Nat := 118140960795 + 541933 * 2 ^ 59
def prefixEnd_541933 : Nat := 4983230072969 + 3 ^ 40 * 541933 * 2
def baseEnd_541933 : Nat := 82450996009817309139319

theorem tailTrace_541933 : CollatzResearch.WordTrace tailWord_541933 prefixEnd_541933 82450996009817309139319 := by
  unfold tailWord_541933
  simp only [CollatzResearch.WordTrace]
  refine ⟨19765920345676770632846453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13177280230451180421897635 19765920345676770632846453)
  ·
    refine ⟨1853055032407197246829355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19765920345676770632846453 1853055032407197246829355)
    ·
      refine ⟨2779582548610795870244033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1853055032407197246829355 2779582548610795870244033)
      ·
        refine ⟨2084686911458096902683025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2779582548610795870244033 2084686911458096902683025)
        ·
          refine ⟨1563515183593572677012269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2084686911458096902683025 1563515183593572677012269)
          ·
            refine ⟨586318193847589753879601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1563515183593572677012269 586318193847589753879601)
            ·
              refine ⟨439738645385692315409701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586318193847589753879601 439738645385692315409701)
              ·
                refine ⟨82450996009817309139319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 439738645385692315409701 82450996009817309139319)
                ·
                  rfl

theorem cell20_541933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 4].length) (baseStart_541933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541933 prefixEnd_541933 := by exact prefixLift 541933
  have htrace : WordTrace (prefixWord ++ tailWord_541933) baseStart_541933 baseEnd_541933 := by
    simpa [prefixWord, tailWord_541933, baseEnd_541933] using wordTrace_append hprefix tailTrace_541933
  have hstable : (prefixWord ++ tailWord_541933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541933).length < 2 ^ (prefixWord ++ tailWord_541933).sum := by decide
  have hdescent : baseEnd_541933 < baseStart_541933 := by decide
  rcases family_descends (prefixWord ++ tailWord_541933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541964 : List Nat := [2, 2, 1, 2, 2, 4, 3, 2, 2]
def baseStart_541964 : Nat := 118140960795 + 541964 * 2 ^ 59
def prefixEnd_541964 : Nat := 4983230072969 + 3 ^ 40 * 541964 * 2
def baseEnd_541964 : Nat := 247367137274153597384497

theorem tailTrace_541964 : CollatzResearch.WordTrace tailWord_541964 prefixEnd_541964 247367137274153597384497 := by
  unfold tailWord_541964
  simp only [CollatzResearch.WordTrace]
  refine ⟨9883525504282231463612473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13178034005709641951483297 9883525504282231463612473)
  ·
    refine ⟨7412644128211673597709355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9883525504282231463612473 7412644128211673597709355)
    ·
      refine ⟨11118966192317510396564033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7412644128211673597709355 11118966192317510396564033)
      ·
        refine ⟨8339224644238132797423025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11118966192317510396564033 8339224644238132797423025)
        ·
          refine ⟨6254418483178599598067269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8339224644238132797423025 6254418483178599598067269)
          ·
            refine ⟨1172703465595987424637613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6254418483178599598067269 1172703465595987424637613)
            ·
              refine ⟨439763799598495284239105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1172703465595987424637613 439763799598495284239105)
              ·
                refine ⟨329822849698871463179329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439763799598495284239105 329822849698871463179329)
                ·
                  refine ⟨247367137274153597384497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329822849698871463179329 247367137274153597384497)
                  ·
                    rfl

theorem cell20_541964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_541964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541964 prefixEnd_541964 := by exact prefixLift 541964
  have htrace : WordTrace (prefixWord ++ tailWord_541964) baseStart_541964 baseEnd_541964 := by
    simpa [prefixWord, tailWord_541964, baseEnd_541964] using wordTrace_append hprefix tailTrace_541964
  have hstable : (prefixWord ++ tailWord_541964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541964).length < 2 ^ (prefixWord ++ tailWord_541964).sum := by decide
  have hdescent : baseEnd_541964 < baseStart_541964 := by decide
  rcases family_descends (prefixWord ++ tailWord_541964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541975 : List Nat := [1, 1, 3, 4, 1, 1, 4, 5]
def baseStart_541975 : Nat := 118140960795 + 541975 * 2 ^ 59
def prefixEnd_541975 : Nat := 4983230072969 + 3 ^ 40 * 541975 * 2
def baseEnd_541975 : Nat := 82457385991295482672595

theorem tailTrace_541975 : CollatzResearch.WordTrace tailWord_541975 prefixEnd_541975 82457385991295482672595 := by
  unfold tailWord_541975
  simp only [CollatzResearch.WordTrace]
  refine ⟨19767452211524611805875379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13178301474349741203916919 19767452211524611805875379)
  ·
    refine ⟨29651178317286917708813069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19767452211524611805875379 29651178317286917708813069)
    ·
      refine ⟨11119191868982594140804901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29651178317286917708813069 11119191868982594140804901)
      ·
        refine ⟨2084848475434236401400919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11119191868982594140804901 2084848475434236401400919)
        ·
          refine ⟨3127272713151354602101379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2084848475434236401400919 3127272713151354602101379)
          ·
            refine ⟨4690909069727031903152069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3127272713151354602101379 4690909069727031903152069)
            ·
              refine ⟨879545450573818481841013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4690909069727031903152069 879545450573818481841013)
              ·
                refine ⟨82457385991295482672595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 879545450573818481841013 82457385991295482672595)
                ·
                  rfl

theorem cell20_541975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 5].length) (baseStart_541975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541975 prefixEnd_541975 := by exact prefixLift 541975
  have htrace : WordTrace (prefixWord ++ tailWord_541975) baseStart_541975 baseEnd_541975 := by
    simpa [prefixWord, tailWord_541975, baseEnd_541975] using wordTrace_append hprefix tailTrace_541975
  have hstable : (prefixWord ++ tailWord_541975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541975).length < 2 ^ (prefixWord ++ tailWord_541975).sum := by decide
  have hdescent : baseEnd_541975 < baseStart_541975 := by decide
  rcases family_descends (prefixWord ++ tailWord_541975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_541978 : List Nat := [3, 1, 1, 3, 3, 1, 4, 1, 3]
def baseStart_541978 : Nat := 118140960795 + 541978 * 2 ^ 59
def prefixEnd_541978 : Nat := 4983230072969 + 3 ^ 40 * 541978 * 2
def baseEnd_541978 : Nat := 247373527255631770917773

theorem tailTrace_541978 : CollatzResearch.WordTrace tailWord_541978 prefixEnd_541978 247373527255631770917773 := by
  unfold tailWord_541978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4941890407628435829558647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13178374420342495545489725 4941890407628435829558647)
  ·
    refine ⟨7412835611442653744337971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4941890407628435829558647 7412835611442653744337971)
    ·
      refine ⟨11119253417163980616506957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7412835611442653744337971 11119253417163980616506957)
      ·
        refine ⟨4169720031436492731190109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11119253417163980616506957 4169720031436492731190109)
        ·
          refine ⟨1563645011788684774196291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4169720031436492731190109 1563645011788684774196291)
          ·
            refine ⟨2345467517683027161294437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563645011788684774196291 2345467517683027161294437)
            ·
              refine ⟨439775159565567592742707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2345467517683027161294437 439775159565567592742707)
              ·
                refine ⟨659662739348351389114061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439775159565567592742707 659662739348351389114061)
                ·
                  refine ⟨247373527255631770917773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659662739348351389114061 247373527255631770917773)
                  ·
                    rfl

theorem cell20_541978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_541978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_541978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_541978 prefixEnd_541978 := by exact prefixLift 541978
  have htrace : WordTrace (prefixWord ++ tailWord_541978) baseStart_541978 baseEnd_541978 := by
    simpa [prefixWord, tailWord_541978, baseEnd_541978] using wordTrace_append hprefix tailTrace_541978
  have hstable : (prefixWord ++ tailWord_541978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_541978).length < 2 ^ (prefixWord ++ tailWord_541978).sum := by decide
  have hdescent : baseEnd_541978 < baseStart_541978 := by decide
  rcases family_descends (prefixWord ++ tailWord_541978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542013 : List Nat := [1, 4, 1, 5, 9]
def baseStart_542013 : Nat := 118140960795 + 542013 * 2 ^ 59
def prefixEnd_542013 : Nat := 4983230072969 + 3 ^ 40 * 542013 * 2
def baseEnd_542013 : Nat := 3054191385300335861123

theorem tailTrace_542013 : CollatzResearch.WordTrace tailWord_542013 prefixEnd_542013 3054191385300335861123 := by
  unfold tailWord_542013
  simp only [CollatzResearch.WordTrace]
  refine ⟨19768838185386944295758693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13179225456924629530505795 19768838185386944295758693)
  ·
    refine ⟨3706657159760052055454755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19768838185386944295758693 3706657159760052055454755)
    ·
      refine ⟨5559985739640078083182133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3706657159760052055454755 5559985739640078083182133)
      ·
        refine ⟨521248663091257320298325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5559985739640078083182133 521248663091257320298325)
        ·
          refine ⟨3054191385300335861123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 521248663091257320298325 3054191385300335861123)
          ·
            rfl

theorem cell20_542013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 9].length) (baseStart_542013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542013 prefixEnd_542013 := by exact prefixLift 542013
  have htrace : WordTrace (prefixWord ++ tailWord_542013) baseStart_542013 baseEnd_542013 := by
    simpa [prefixWord, tailWord_542013, baseEnd_542013] using wordTrace_append hprefix tailTrace_542013
  have hstable : (prefixWord ++ tailWord_542013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542013).length < 2 ^ (prefixWord ++ tailWord_542013).sum := by decide
  have hdescent : baseEnd_542013 < baseStart_542013 := by decide
  rcases family_descends (prefixWord ++ tailWord_542013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542023 : List Nat := [1, 1, 4, 1, 2, 4, 1, 4, 2]
def baseStart_542023 : Nat := 118140960795 + 542023 * 2 ^ 59
def prefixEnd_542023 : Nat := 4983230072969 + 3 ^ 40 * 542023 * 2
def baseEnd_542023 : Nat := 247394066481811614417589

theorem tailTrace_542023 : CollatzResearch.WordTrace tailWord_542023 prefixEnd_542023 247394066481811614417589 := by
  unfold tailWord_542023
  simp only [CollatzResearch.WordTrace]
  refine ⟨19769202915350716003622723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13179468610233810669081815 19769202915350716003622723)
  ·
    refine ⟨29653804373026074005434085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19769202915350716003622723 29653804373026074005434085)
    ·
      refine ⟨5560088319942388876018891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29653804373026074005434085 5560088319942388876018891)
      ·
        refine ⟨8340132479913583314028337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5560088319942388876018891 8340132479913583314028337)
        ·
          refine ⟨6255099359935187485521253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8340132479913583314028337 6255099359935187485521253)
          ·
            refine ⟨1172831129987847653535235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6255099359935187485521253 1172831129987847653535235)
            ·
              refine ⟨1759246694981771480302853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172831129987847653535235 1759246694981771480302853)
              ·
                refine ⟨329858755309082152556785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1759246694981771480302853 329858755309082152556785)
                ·
                  refine ⟨247394066481811614417589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329858755309082152556785 247394066481811614417589)
                  ·
                    rfl

theorem cell20_542023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4, 2].length) (baseStart_542023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542023 prefixEnd_542023 := by exact prefixLift 542023
  have htrace : WordTrace (prefixWord ++ tailWord_542023) baseStart_542023 baseEnd_542023 := by
    simpa [prefixWord, tailWord_542023, baseEnd_542023] using wordTrace_append hprefix tailTrace_542023
  have hstable : (prefixWord ++ tailWord_542023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542023).length < 2 ^ (prefixWord ++ tailWord_542023).sum := by decide
  have hdescent : baseEnd_542023 < baseStart_542023 := by decide
  rcases family_descends (prefixWord ++ tailWord_542023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542037 : List Nat := [1, 3, 2, 2, 3, 1, 2, 3, 3]
def baseStart_542037 : Nat := 118140960795 + 542037 * 2 ^ 59
def prefixEnd_542037 : Nat := 4983230072969 + 3 ^ 40 * 542037 * 2
def baseEnd_542037 : Nat := 247400456463289787950865

theorem tailTrace_542037 : CollatzResearch.WordTrace tailWord_542037 prefixEnd_542037 247400456463289787950865 := by
  unfold tailWord_542037
  simp only [CollatzResearch.WordTrace]
  refine ⟨19769713537299996394632365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13179809024866664263088243 19769713537299996394632365)
  ·
    refine ⟨7413642576487498647987137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19769713537299996394632365 7413642576487498647987137)
    ·
      refine ⟨5560231932365623985990353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7413642576487498647987137 5560231932365623985990353)
      ·
        refine ⟨4170173949274217989492765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5560231932365623985990353 4170173949274217989492765)
        ·
          refine ⟨1563815230977831746059787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4170173949274217989492765 1563815230977831746059787)
          ·
            refine ⟨2345722846466747619089681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563815230977831746059787 2345722846466747619089681)
            ·
              refine ⟨1759292134850060714317261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2345722846466747619089681 1759292134850060714317261)
              ·
                refine ⟨659734550568772767868973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1759292134850060714317261 659734550568772767868973)
                ·
                  refine ⟨247400456463289787950865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 659734550568772767868973 247400456463289787950865)
                  ·
                    rfl

theorem cell20_542037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_542037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542037 prefixEnd_542037 := by exact prefixLift 542037
  have htrace : WordTrace (prefixWord ++ tailWord_542037) baseStart_542037 baseEnd_542037 := by
    simpa [prefixWord, tailWord_542037, baseEnd_542037] using wordTrace_append hprefix tailTrace_542037
  have hstable : (prefixWord ++ tailWord_542037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542037).length < 2 ^ (prefixWord ++ tailWord_542037).sum := by decide
  have hdescent : baseEnd_542037 < baseStart_542037 := by decide
  rcases family_descends (prefixWord ++ tailWord_542037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542061 : List Nat := [1, 5, 1, 1, 1, 3, 1, 5, 2]
def baseStart_542061 : Nat := 118140960795 + 542061 * 2 ^ 59
def prefixEnd_542061 : Nat := 4983230072969 + 3 ^ 40 * 542061 * 2
def baseEnd_542061 : Nat := 247411410717252371150767

theorem tailTrace_542061 : CollatzResearch.WordTrace tailWord_542061 prefixEnd_542061 247411410717252371150767 := by
  unfold tailWord_542061
  simp only [CollatzResearch.WordTrace]
  refine ⟨19770588889213048493506037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13180392592808698995670691 19770588889213048493506037)
  ·
    refine ⟨1853492708363723296266191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19770588889213048493506037 1853492708363723296266191)
    ·
      refine ⟨2780239062545584944399287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1853492708363723296266191 2780239062545584944399287)
      ·
        refine ⟨4170358593818377416598931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2780239062545584944399287 4170358593818377416598931)
        ·
          refine ⟨6255537890727566124898397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4170358593818377416598931 6255537890727566124898397)
          ·
            refine ⟨2345826709022837296836899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6255537890727566124898397 2345826709022837296836899)
            ·
              refine ⟨3518740063534255945255349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345826709022837296836899 3518740063534255945255349)
              ·
                refine ⟨329881880956336494867689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3518740063534255945255349 329881880956336494867689)
                ·
                  refine ⟨247411410717252371150767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329881880956336494867689 247411410717252371150767)
                  ·
                    rfl

theorem cell20_542061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_542061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542061 prefixEnd_542061 := by exact prefixLift 542061
  have htrace : WordTrace (prefixWord ++ tailWord_542061) baseStart_542061 baseEnd_542061 := by
    simpa [prefixWord, tailWord_542061, baseEnd_542061] using wordTrace_append hprefix tailTrace_542061
  have hstable : (prefixWord ++ tailWord_542061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542061).length < 2 ^ (prefixWord ++ tailWord_542061).sum := by decide
  have hdescent : baseEnd_542061 < baseStart_542061 := by decide
  rcases family_descends (prefixWord ++ tailWord_542061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542137 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 4]
def baseStart_542137 : Nat := 118140960795 + 542137 * 2 ^ 59
def prefixEnd_542137 : Nat := 4983230072969 + 3 ^ 40 * 542137 * 2
def baseEnd_542137 : Nat := 247446099188133884617123

theorem tailTrace_542137 : CollatzResearch.WordTrace tailWord_542137 prefixEnd_542137 247446099188133884617123 := by
  unfold tailWord_542137
  simp only [CollatzResearch.WordTrace]
  refine ⟨19773360836937713473272665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13182240557958475648848443 19773360836937713473272665)
  ·
    refine ⟨14830020627703285104954499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19773360836937713473272665 14830020627703285104954499)
    ·
      refine ⟨22245030941554927657431749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14830020627703285104954499 22245030941554927657431749)
      ·
        refine ⟨4170943301541548935768453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22245030941554927657431749 4170943301541548935768453)
        ·
          refine ⟨782051869039040425456585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4170943301541548935768453 782051869039040425456585)
          ·
            refine ⟨586538901779280319092439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 782051869039040425456585 586538901779280319092439)
            ·
              refine ⟨879808352668920478638659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 586538901779280319092439 879808352668920478638659)
              ·
                refine ⟨1319712529003380717957989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879808352668920478638659 1319712529003380717957989)
                ·
                  refine ⟨247446099188133884617123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1319712529003380717957989 247446099188133884617123)
                  ·
                    rfl

theorem cell20_542137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_542137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542137 prefixEnd_542137 := by exact prefixLift 542137
  have htrace : WordTrace (prefixWord ++ tailWord_542137) baseStart_542137 baseEnd_542137 := by
    simpa [prefixWord, tailWord_542137, baseEnd_542137] using wordTrace_append hprefix tailTrace_542137
  have hstable : (prefixWord ++ tailWord_542137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542137).length < 2 ^ (prefixWord ++ tailWord_542137).sum := by decide
  have hdescent : baseEnd_542137 < baseStart_542137 := by decide
  rcases family_descends (prefixWord ++ tailWord_542137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542186 : List Nat := [3, 1, 3, 1, 12]
def baseStart_542186 : Nat := 118140960795 + 542186 * 2 ^ 59
def prefixEnd_542186 : Nat := 4983230072969 + 3 ^ 40 * 542186 * 2
def baseEnd_542186 : Nat := 3055166223744536938069

theorem tailTrace_542186 : CollatzResearch.WordTrace tailWord_542186 prefixEnd_542186 3055166223744536938069 := by
  unfold tailWord_542186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4943787003440048710451603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13183432009173463227870941 4943787003440048710451603)
  ·
    refine ⟨7415680505160073065677405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4943787003440048710451603 7415680505160073065677405)
    ·
      refine ⟨2780880189435027399629027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7415680505160073065677405 2780880189435027399629027)
      ·
        refine ⟨4171320284152541099443541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2780880189435027399629027 4171320284152541099443541)
        ·
          refine ⟨3055166223744536938069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4171320284152541099443541 3055166223744536938069)
          ·
            rfl

theorem cell20_542186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 12].length) (baseStart_542186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542186 prefixEnd_542186 := by exact prefixLift 542186
  have htrace : WordTrace (prefixWord ++ tailWord_542186) baseStart_542186 baseEnd_542186 := by
    simpa [prefixWord, tailWord_542186, baseEnd_542186] using wordTrace_append hprefix tailTrace_542186
  have hstable : (prefixWord ++ tailWord_542186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542186).length < 2 ^ (prefixWord ++ tailWord_542186).sum := by decide
  have hdescent : baseEnd_542186 < baseStart_542186 := by decide
  rcases family_descends (prefixWord ++ tailWord_542186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542192 : List Nat := [2, 1, 1, 1, 3, 6, 2, 2, 2]
def baseStart_542192 : Nat := 118140960795 + 542192 * 2 ^ 59
def prefixEnd_542192 : Nat := 4983230072969 + 3 ^ 40 * 542192 * 2
def baseEnd_542192 : Nat := 247471202686798137783565

theorem tailTrace_542192 : CollatzResearch.WordTrace tailWord_542192 prefixEnd_542192 247471202686798137783565 := by
  unfold tailWord_542192
  simp only [CollatzResearch.WordTrace]
  refine ⟨9887683425869228933262415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13183577901158971911016553 9887683425869228933262415)
  ·
    refine ⟨14831525138803843399893623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9887683425869228933262415 14831525138803843399893623)
    ·
      refine ⟨22247287708205765099840435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14831525138803843399893623 22247287708205765099840435)
      ·
        refine ⟨33370931562308647649760653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22247287708205765099840435 33370931562308647649760653)
        ·
          refine ⟨12514099335865742868660245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33370931562308647649760653 12514099335865742868660245)
          ·
            refine ⟨586598406368706696968449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12514099335865742868660245 586598406368706696968449)
            ·
              refine ⟨439948804776530022726337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586598406368706696968449 439948804776530022726337)
              ·
                refine ⟨329961603582397517044753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439948804776530022726337 329961603582397517044753)
                ·
                  refine ⟨247471202686798137783565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 329961603582397517044753 247471202686798137783565)
                  ·
                    rfl

theorem cell20_542192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 2].length) (baseStart_542192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542192 prefixEnd_542192 := by exact prefixLift 542192
  have htrace : WordTrace (prefixWord ++ tailWord_542192) baseStart_542192 baseEnd_542192 := by
    simpa [prefixWord, tailWord_542192, baseEnd_542192] using wordTrace_append hprefix tailTrace_542192
  have hstable : (prefixWord ++ tailWord_542192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542192).length < 2 ^ (prefixWord ++ tailWord_542192).sum := by decide
  have hdescent : baseEnd_542192 < baseStart_542192 := by decide
  rcases family_descends (prefixWord ++ tailWord_542192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542217 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 4]
def baseStart_542217 : Nat := 118140960795 + 542217 * 2 ^ 59
def prefixEnd_542217 : Nat := 4983230072969 + 3 ^ 40 * 542217 * 2
def baseEnd_542217 : Nat := 247482613368009161950129

theorem tailTrace_542217 : CollatzResearch.WordTrace tailWord_542217 prefixEnd_542217 247482613368009161950129 := by
  unfold tailWord_542217
  simp only [CollatzResearch.WordTrace]
  refine ⟨19776278676647887136184905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13184185784431924757456603 19776278676647887136184905)
  ·
    refine ⟨14832209007485915352138679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19776278676647887136184905 14832209007485915352138679)
    ·
      refine ⟨22248313511228873028208019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14832209007485915352138679 22248313511228873028208019)
      ·
        refine ⟨33372470266843309542312029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22248313511228873028208019 33372470266843309542312029)
        ·
          refine ⟨12514676350066241078367011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33372470266843309542312029 12514676350066241078367011)
          ·
            refine ⟨18772014525099361617550517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12514676350066241078367011 18772014525099361617550517)
            ·
              refine ⟨1759876361728065151645361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18772014525099361617550517 1759876361728065151645361)
              ·
                refine ⟨1319907271296048863734021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1759876361728065151645361 1319907271296048863734021)
                ·
                  refine ⟨247482613368009161950129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1319907271296048863734021 247482613368009161950129)
                  ·
                    rfl

theorem cell20_542217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_542217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542217 prefixEnd_542217 := by exact prefixLift 542217
  have htrace : WordTrace (prefixWord ++ tailWord_542217) baseStart_542217 baseEnd_542217 := by
    simpa [prefixWord, tailWord_542217, baseEnd_542217] using wordTrace_append hprefix tailTrace_542217
  have hstable : (prefixWord ++ tailWord_542217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542217).length < 2 ^ (prefixWord ++ tailWord_542217).sum := by decide
  have hdescent : baseEnd_542217 < baseStart_542217 := by decide
  rcases family_descends (prefixWord ++ tailWord_542217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542220 : List Nat := [2, 2, 1, 2, 5, 1, 3, 4]
def baseStart_542220 : Nat := 118140960795 + 542220 * 2 ^ 59
def prefixEnd_542220 : Nat := 4983230072969 + 3 ^ 40 * 542220 * 2
def baseEnd_542220 : Nat := 82494660883251494950039

theorem tailTrace_542220 : CollatzResearch.WordTrace tailWord_542220 prefixEnd_542220 82494660883251494950039 := by
  unfold tailWord_542220
  simp only [CollatzResearch.WordTrace]
  refine ⟨9888194047818509324272057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13184258730424679099029409 9888194047818509324272057)
  ·
    refine ⟨7416145535863881993204043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9888194047818509324272057 7416145535863881993204043)
    ·
      refine ⟨11124218303795822989806065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7416145535863881993204043 11124218303795822989806065)
      ·
        refine ⟨8343163727846867242354549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11124218303795822989806065 8343163727846867242354549)
        ·
          refine ⟨782171599485643803970739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8343163727846867242354549 782171599485643803970739)
          ·
            refine ⟨1173257399228465705956109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782171599485643803970739 1173257399228465705956109)
            ·
              refine ⟨439971524710674639733541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1173257399228465705956109 439971524710674639733541)
              ·
                refine ⟨82494660883251494950039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 439971524710674639733541 82494660883251494950039)
                ·
                  rfl

theorem cell20_542220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_542220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542220 prefixEnd_542220 := by exact prefixLift 542220
  have htrace : WordTrace (prefixWord ++ tailWord_542220) baseStart_542220 baseEnd_542220 := by
    simpa [prefixWord, tailWord_542220, baseEnd_542220] using wordTrace_append hprefix tailTrace_542220
  have hstable : (prefixWord ++ tailWord_542220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542220).length < 2 ^ (prefixWord ++ tailWord_542220).sum := by decide
  have hdescent : baseEnd_542220 < baseStart_542220 := by decide
  rcases family_descends (prefixWord ++ tailWord_542220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_542279 : List Nat := [1, 1, 4, 1, 5, 1, 1, 6]
def baseStart_542279 : Nat := 118140960795 + 542279 * 2 ^ 59
def prefixEnd_542279 : Nat := 4983230072969 + 3 ^ 40 * 542279 * 2
def baseEnd_542279 : Nat := 82503637285804167294403

theorem tailTrace_542279 : CollatzResearch.WordTrace tailWord_542279 prefixEnd_542279 82503637285804167294403 := by
  unfold tailWord_542279
  simp only [CollatzResearch.WordTrace]
  refine ⟨19778540002423271724941891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13185693334948847816627927 19778540002423271724941891)
  ·
    refine ⟨29667810003634907587412837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19778540002423271724941891 29667810003634907587412837)
    ·
      refine ⟨5562714375681545172639907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29667810003634907587412837 5562714375681545172639907)
      ·
        refine ⟨8344071563522317758959861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5562714375681545172639907 8344071563522317758959861)
        ·
          refine ⟨782256709080217289902487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8344071563522317758959861 782256709080217289902487)
          ·
            refine ⟨1173385063620325934853731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782256709080217289902487 1173385063620325934853731)
            ·
              refine ⟨1760077595430488902280597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1173385063620325934853731 1760077595430488902280597)
              ·
                refine ⟨82503637285804167294403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1760077595430488902280597 82503637285804167294403)
                ·
                  rfl

theorem cell20_542279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 6].length) (baseStart_542279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_542279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_542279 prefixEnd_542279 := by exact prefixLift 542279
  have htrace : WordTrace (prefixWord ++ tailWord_542279) baseStart_542279 baseEnd_542279 := by
    simpa [prefixWord, tailWord_542279, baseEnd_542279] using wordTrace_append hprefix tailTrace_542279
  have hstable : (prefixWord ++ tailWord_542279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_542279).length < 2 ^ (prefixWord ++ tailWord_542279).sum := by decide
  have hdescent : baseEnd_542279 < baseStart_542279 := by decide
  rcases family_descends (prefixWord ++ tailWord_542279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
